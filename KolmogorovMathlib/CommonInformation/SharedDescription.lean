import KolmogorovMathlib.CommonInformation.OverlapGeometry
import KolmogorovMathlib.CommonInformation.Splitting
import KolmogorovMathlib.Foundation.NatEncoding

/-!
# Common Information: conditional-complexity decoder leaves

Reusable plain conditional-complexity decoders for the Exercise 307 overlap
argument.  Indices are always supplied as *binary* codes (`Nat.bits`, decoded by
`decodeBits`), never the unary `natCode`, so that an index bounded by `|w|` costs
only `O(log |w|)` program bits.

* `condK_slice_le` — any contiguous slice `(w.drop i).take n` of `w` is
  recoverable from `w` alone with a program of `O(log |w|)` bits.  This is the
  decoder used for the overlap-block → common-string direction: the shared block
  is a slice of the incompressible representation `u`.
-/

namespace Kolmogorov

/-- Any contiguous slice `(w.drop i).take n` of `w` (with start and length
bounded by `|w|`) is recoverable from `w` with a program of only
`logSlack c (|w| + 1) = O(log |w|)` bits.  The whole program is the pair code of
the binary representations of `i` and `n`; the decompressor decodes them and
slices the context. -/
theorem condK_slice_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (w : BitString) (i n : Nat),
      i ≤ w.length → n ≤ w.length →
      condK V ((w.drop i).take n) w ≤ (logSlack c (w.length + 1) : ENat) := by
  -- The slice decompressor: the program codes `(bits i, bits n)`, the context is `w`.
  let D : Map := fun pr =>
    Part.some ((pr.2.drop (decodeBits (decodeFirst pr.1))).take
      (decodeBits (decodeSecond pr.1)))
  have hf : Computable (fun pr : BitString × BitString =>
      (pr.2.drop (decodeBits (decodeFirst pr.1))).take
        (decodeBits (decodeSecond pr.1))) :=
    (Primrec.list_take.comp
      (primrecDecodeBits.comp (decodeSecond_primrec'.comp Primrec.fst))
      (Primrec.list_drop.comp
        (primrecDecodeBits.comp (decodeFirst_primrec'.comp Primrec.fst))
        Primrec.snd)).to_comp
  have hD : isDecompressor D := Computable.partrec hf
  obtain ⟨c₀, hc₀⟩ := hV.2 D hD
  refine ⟨c₀ + 3, fun w i n hi hn => ?_⟩
  set prog : BitString := pairCode (Nat.bits i) (Nat.bits n) with hprog
  -- The slice is produced by the binary-coded index pair.
  have hDprod : produces D prog w ((w.drop i).take n) := by
    change ((w.drop i).take n) ∈
      Part.some ((w.drop (decodeBits (decodeFirst prog))).take
        (decodeBits (decodeSecond prog)))
    rw [hprog, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits,
      decodeBits_natBits]
    exact Part.mem_some _
  have hlen : condK D ((w.drop i).take n) w ≤ (prog.length : ENat) :=
    sInf_le ⟨prog, hDprod, rfl⟩
  have hVbound : condK V ((w.drop i).take n) w ≤ (prog.length : ENat) + (c₀ : ENat) :=
    (hc₀ _ w).trans (by gcongr)
  -- Numeric bound: `|prog| + c₀ ≤ logSlack (c₀ + 3) (|w| + 1)`.
  have hprogLen : prog.length
      = (Nat.bits i).length + 1 + (Nat.bits i).length + (Nat.bits n).length := by
    rw [hprog]; exact length_pairCode _ _
  have hiL : (Nat.bits i).length ≤ (Nat.bits (w.length + 1)).length :=
    length_natBits_mono (by omega)
  have hnL : (Nat.bits n).length ≤ (Nat.bits (w.length + 1)).length :=
    length_natBits_mono (by omega)
  have hfinal : prog.length + c₀ ≤ logSlack (c₀ + 3) (w.length + 1) := by
    unfold logSlack
    rw [hprogLen]
    set L := (Nat.bits (w.length + 1)).length with hLdef
    have hexpand : (c₀ + 3) * L + (c₀ + 3) = 3 * L + (c₀ * L + c₀ + 3) := by ring
    rw [hexpand]
    omega
  calc
    condK V ((w.drop i).take n) w ≤ (prog.length : ENat) + (c₀ : ENat) := hVbound
    _ = ((prog.length + c₀ : Nat) : ENat) := by push_cast; ring
    _ ≤ (logSlack (c₀ + 3) (w.length + 1) : ENat) := by exact_mod_cast hfinal

/-- **Reverse split-indexed two-stage decoder.**  If `p` produces `z`
unconditionally and `a` produces `x` given `z`, then `x` is recoverable from the
literal concatenation `a ++ p` with a program of only `logSlack c (|a| + 1)`
bits: the binary code of the split position `|a|`.  The decompressor splits
`a ++ p` at that position, runs the suffix `p` on the empty condition to obtain
`z`, then runs the prefix `a` on condition `z`.  No unlabelled-split search is
performed, and the public two-stage machinery of Theorem 222 is untouched. -/
theorem condK_output_given_splitIndexed_reverseConcat_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ a p z x : BitString,
      produces V p [] z →
      produces V a z x →
      condK V x (a ++ p) ≤ (logSlack c (a.length + 1) : ENat) := by
  -- Program = binary split index; suffix runs on `[]`, prefix runs on its output.
  let D : Map := fun pr =>
    (V (pr.2.drop (decodeBits pr.1), [])).bind
      (fun z => V (pr.2.take (decodeBits pr.1), z))
  have hFirst : Partrec (fun pr : BitString × BitString =>
      V (pr.2.drop (decodeBits pr.1), [])) :=
    Partrec.comp hV.1 (Computable.pair
      ((Primrec.list_drop.comp (primrecDecodeBits.comp Primrec.fst) Primrec.snd).to_comp)
      (Computable.const []))
  have hSecond : Partrec (fun q : (BitString × BitString) × BitString =>
      V (q.1.2.take (decodeBits q.1.1), q.2)) :=
    Partrec.comp hV.1 (Computable.pair
      ((Primrec.list_take.comp (primrecDecodeBits.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst)).to_comp)
      Computable.snd)
  have hD : isDecompressor D := Partrec.bind hFirst hSecond
  obtain ⟨c₀, hc₀⟩ := hV.2 D hD
  refine ⟨c₀ + 2, fun a p z x hp ha => ?_⟩
  set prog : BitString := Nat.bits a.length with hprog
  have hDprod : produces D prog (a ++ p) x := by
    change x ∈ (V ((a ++ p).drop (decodeBits prog), [])).bind
      (fun z => V ((a ++ p).take (decodeBits prog), z))
    rw [hprog]
    simp only [decodeBits_natBits, List.take_left, List.drop_left]
    exact Part.mem_bind_iff.mpr ⟨z, hp, ha⟩
  have hlen : condK D x (a ++ p) ≤ (prog.length : ENat) :=
    sInf_le ⟨prog, hDprod, rfl⟩
  have hVbound : condK V x (a ++ p) ≤ (prog.length : ENat) + (c₀ : ENat) :=
    (hc₀ x (a ++ p)).trans (by gcongr)
  have hprogLen : prog.length ≤ (Nat.bits (a.length + 1)).length := by
    rw [hprog]; exact length_natBits_mono (by omega)
  have hfinal : prog.length + c₀ ≤ logSlack (c₀ + 2) (a.length + 1) := by
    unfold logSlack
    set L := (Nat.bits (a.length + 1)).length with hLdef
    have hexpand : (c₀ + 2) * L + (c₀ + 2) = L + (c₀ * L + L + c₀ + 2) := by ring
    rw [hexpand]
    omega
  calc
    condK V x (a ++ p) ≤ (prog.length : ENat) + (c₀ : ENat) := hVbound
    _ = ((prog.length + c₀ : Nat) : ENat) := by push_cast; ring
    _ ≤ (logSlack (c₀ + 2) (a.length + 1) : ENat) := by exact_mod_cast hfinal

/-- **Forward split-indexed two-stage decoder.**  If `p` produces `z`
unconditionally and `b` produces `y` given `z`, then `y` is recoverable from the
literal concatenation `p ++ b` with a program of only `logSlack c (|p| + 1)`
bits: the binary code of the split position `|p|`.  The decompressor splits
`p ++ b` at that position, runs the prefix `p` on the empty condition to obtain
`z`, then runs the suffix `b` on condition `z`. -/
theorem condK_output_given_splitIndexed_forwardConcat_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ p b z y : BitString,
      produces V p [] z →
      produces V b z y →
      condK V y (p ++ b) ≤ (logSlack c (p.length + 1) : ENat) := by
  -- Program = binary split index; prefix runs on `[]`, suffix runs on its output.
  let D : Map := fun pr =>
    (V (pr.2.take (decodeBits pr.1), [])).bind
      (fun z => V (pr.2.drop (decodeBits pr.1), z))
  have hFirst : Partrec (fun pr : BitString × BitString =>
      V (pr.2.take (decodeBits pr.1), [])) :=
    Partrec.comp hV.1 (Computable.pair
      ((Primrec.list_take.comp (primrecDecodeBits.comp Primrec.fst) Primrec.snd).to_comp)
      (Computable.const []))
  have hSecond : Partrec (fun q : (BitString × BitString) × BitString =>
      V (q.1.2.drop (decodeBits q.1.1), q.2)) :=
    Partrec.comp hV.1 (Computable.pair
      ((Primrec.list_drop.comp (primrecDecodeBits.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst)).to_comp)
      Computable.snd)
  have hD : isDecompressor D := Partrec.bind hFirst hSecond
  obtain ⟨c₀, hc₀⟩ := hV.2 D hD
  refine ⟨c₀ + 2, fun p b z y hp hb => ?_⟩
  set prog : BitString := Nat.bits p.length with hprog
  have hDprod : produces D prog (p ++ b) y := by
    change y ∈ (V ((p ++ b).take (decodeBits prog), [])).bind
      (fun z => V ((p ++ b).drop (decodeBits prog), z))
    rw [hprog]
    simp only [decodeBits_natBits, List.take_left, List.drop_left]
    exact Part.mem_bind_iff.mpr ⟨z, hp, hb⟩
  have hlen : condK D y (p ++ b) ≤ (prog.length : ENat) :=
    sInf_le ⟨prog, hDprod, rfl⟩
  have hVbound : condK V y (p ++ b) ≤ (prog.length : ENat) + (c₀ : ENat) :=
    (hc₀ y (p ++ b)).trans (by gcongr)
  have hprogLen : prog.length ≤ (Nat.bits (p.length + 1)).length := by
    rw [hprog]; exact length_natBits_mono (by omega)
  have hfinal : prog.length + c₀ ≤ logSlack (c₀ + 2) (p.length + 1) := by
    unfold logSlack
    set L := (Nat.bits (p.length + 1)).length with hLdef
    have hexpand : (c₀ + 2) * L + (c₀ + 2) = L + (c₀ * L + L + c₀ + 2) := by ring
    rw [hexpand]
    omega
  calc
    condK V y (p ++ b) ≤ (prog.length : ENat) + (c₀ : ENat) := hVbound
    _ = ((prog.length + c₀ : Nat) : ENat) := by push_cast; ring
    _ ≤ (logSlack (c₀ + 2) (p.length + 1) : ENat) := by exact_mod_cast hfinal

theorem resizeToLength_equivalent
    (V : Map) (hV : isOptimalConditional V) :
  ∃ C, ∀ w n r,
    NatCloseWithin w.length n r →
    PlainEquivalentWithin V w (resizeToLength w n)
      (commonInformationSlack C r (w.length + n + 1)) := by
  -- Resize in the forward direction; the program is the binary target length.
  let resizeD : Map := fun pr =>
    Part.some (resizeToLength pr.2 (decodeBits pr.1))
  have hResize : Computable (fun pr : BitString × BitString =>
      resizeToLength pr.2 (decodeBits pr.1)) := by
    have hn : Primrec (fun pr : BitString × BitString =>
        decodeBits pr.1) :=
      primrecDecodeBits.comp Primrec.fst
    have hwlen : Primrec (fun pr : BitString × BitString =>
        pr.2.length) :=
      Primrec.list_length.comp Primrec.snd
    have htake : Primrec (fun pr : BitString × BitString =>
        pr.2.take (decodeBits pr.1)) :=
      Primrec.list_take.comp hn Primrec.snd
    have hpad : Primrec (fun pr : BitString × BitString =>
        List.replicate (decodeBits pr.1 - pr.2.length) false) :=
      Primrec.list_replicate.comp
        (Primrec.nat_sub.comp hn hwlen) (Primrec.const false)
    exact (Primrec.list_append.comp htake hpad).to_comp
  have hResizeD : isDecompressor resizeD :=
    Computable.partrec hResize
  obtain ⟨cResize, hcResize⟩ := hV.2 resizeD hResizeD
  -- Restore the original string from its resized form.  The program contains
  -- the original length and precisely the literal suffix discarded by
  -- truncation; padding needs no literal advice.
  let restoreD : Map := fun pr =>
    Part.some
      (pr.2.take (decodeBits (decodeFirst pr.1)) ++ decodeSecond pr.1)
  have hRestore : Computable (fun pr : BitString × BitString =>
      pr.2.take (decodeBits (decodeFirst pr.1)) ++ decodeSecond pr.1) := by
    exact Computable.list_append.comp
      ((Primrec.list_take.comp
        (primrecDecodeBits.comp
          (decodeFirst_primrec'.comp Primrec.fst)) Primrec.snd).to_comp)
      (decodeSecond_computable.comp Computable.fst)
  have hRestoreD : isDecompressor restoreD :=
    Computable.partrec hRestore
  obtain ⟨cRestore, hcRestore⟩ := hV.2 restoreD hRestoreD
  let C := cResize + cRestore + 3
  refine ⟨C, fun w n r hclose => ?_⟩
  unfold PlainEquivalentWithin
  have hrestore :
      (resizeToLength w n).take w.length ++ w.drop n = w := by
    exact resizeToLength_take_original_append_drop w n
  set restoreProg : BitString :=
    pairCode (Nat.bits w.length) (w.drop n) with hRestoreProg
  have hRestoreProd :
      produces restoreD restoreProg (resizeToLength w n) w := by
    change w ∈ Part.some
      ((resizeToLength w n).take
        (decodeBits (decodeFirst restoreProg)) ++
          decodeSecond restoreProg)
    rw [hRestoreProg, decodeFirst_pairCode, decodeSecond_pairCode,
      decodeBits_natBits, hrestore]
    exact Part.mem_some _
  have hRestoreBound :
      condK V w (resizeToLength w n) ≤
        (restoreProg.length : ENat) + (cRestore : ENat) := by
    calc
      condK V w (resizeToLength w n)
          ≤ condK restoreD w (resizeToLength w n) +
              (cRestore : ENat) :=
        hcRestore w (resizeToLength w n)
      _ ≤ (restoreProg.length : ENat) + (cRestore : ENat) := by
        gcongr
        exact sInf_le ⟨restoreProg, hRestoreProd, rfl⟩
  set resizeProg : BitString := Nat.bits n with hResizeProg
  have hResizeProd :
      produces resizeD resizeProg w (resizeToLength w n) := by
    change resizeToLength w n ∈
      Part.some (resizeToLength w (decodeBits resizeProg))
    rw [hResizeProg, decodeBits_natBits]
    exact Part.mem_some _
  have hResizeBound :
      condK V (resizeToLength w n) w ≤
        (resizeProg.length : ENat) + (cResize : ENat) := by
    calc
      condK V (resizeToLength w n) w
          ≤ condK resizeD (resizeToLength w n) w +
              (cResize : ENat) :=
        hcResize (resizeToLength w n) w
      _ ≤ (resizeProg.length : ENat) + (cResize : ENat) := by
        gcongr
        exact sInf_le ⟨resizeProg, hResizeProd, rfl⟩
  have hDrop : (w.drop n).length ≤ r := by
    rw [List.length_drop]
    unfold NatCloseWithin at hclose
    omega
  have hBitsW :
      (Nat.bits w.length).length ≤
        (Nat.bits (w.length + n + 1)).length :=
    length_natBits_mono (by omega)
  have hBitsN :
      (Nat.bits n).length ≤
        (Nat.bits (w.length + n + 1)).length :=
    length_natBits_mono (by omega)
  have hRestoreLen :
      restoreProg.length =
        2 * (Nat.bits w.length).length + 1 + (w.drop n).length := by
    rw [hRestoreProg, length_pairCode]
    omega
  have hRestoreNat :
      restoreProg.length + cRestore ≤
        commonInformationSlack C r (w.length + n + 1) := by
    unfold commonInformationSlack logSlack
    rw [hRestoreLen]
    dsimp [C]
    nlinarith
  have hResizeNat :
      resizeProg.length + cResize ≤
        commonInformationSlack C r (w.length + n + 1) := by
    unfold commonInformationSlack logSlack
    rw [hResizeProg]
    dsimp [C]
    nlinarith
  constructor
  · exact hRestoreBound.trans (by
      rw [← Nat.cast_add]
      exact_mod_cast hRestoreNat)
  · exact hResizeBound.trans (by
      rw [← Nat.cast_add]
      exact_mod_cast hResizeNat)


theorem condK_pair_from_prefix_suffix_le
    (V : Map) (hV : isOptimalConditional V) :
  ∃ C, ∀ (u x y : BitString) (lx ly a b : Nat),
    lx ≤ u.length → ly ≤ u.length → a ≤ u.length →
    condK V x (u.take lx) ≤ (a : ENat) →
    condK V y (u.drop (u.length - ly)) ≤ (b : ENat) →
    condK V (pairCode x y) u ≤
      (a + b + logSlack C (u.length + 1) : ENat) := by
  -- Program layout:
  --   pairCode (bits |px|)
  --     (pairCode (bits lx) (pairCode (bits ly) (px ++ py))).
  -- Thus the two arbitrary plain programs occur literally once; only their
  -- split and the two condition slices are self-delimited metadata.
  let body : BitString → BitString := fun q =>
    decodeSecond (decodeSecond (decodeSecond q))
  let split : BitString → Nat := fun q =>
    decodeBits (decodeFirst q)
  let prefixLength : BitString → Nat := fun q =>
    decodeBits (decodeFirst (decodeSecond q))
  let suffixLength : BitString → Nat := fun q =>
    decodeBits (decodeFirst (decodeSecond (decodeSecond q)))
  let D : Map := fun pr =>
    (V ((body pr.1).take (split pr.1),
        pr.2.take (prefixLength pr.1))).bind fun x =>
      (V ((body pr.1).drop (split pr.1),
          pr.2.drop (pr.2.length - suffixLength pr.1))).map fun y =>
        pairCode x y
  have hBody : Computable body := by
    exact decodeSecond_computable.comp
      (decodeSecond_computable.comp decodeSecond_computable)
  have hSplit : Computable split := by
    exact decodeBitsComputable.comp decodeFirst_computable
  have hPrefixLength : Computable prefixLength := by
    exact decodeBitsComputable.comp
      (decodeFirst_computable.comp decodeSecond_computable)
  have hSuffixLength : Computable suffixLength := by
    exact decodeBitsComputable.comp
      (decodeFirst_computable.comp
        (decodeSecond_computable.comp decodeSecond_computable))
  have hFirstProgram : Computable (fun pr : BitString × BitString =>
      (body pr.1).take (split pr.1)) :=
    Primrec.list_take.to_comp.comp
      (hSplit.comp Computable.fst) (hBody.comp Computable.fst)
  have hFirstContext : Computable (fun pr : BitString × BitString =>
      pr.2.take (prefixLength pr.1)) :=
    Primrec.list_take.to_comp.comp (hPrefixLength.comp Computable.fst)
      Computable.snd
  have hFirst : Partrec (fun pr : BitString × BitString =>
      V ((body pr.1).take (split pr.1),
        pr.2.take (prefixLength pr.1))) :=
    Partrec.comp hV.1 (hFirstProgram.pair hFirstContext)
  have hSecondProgram :
      Computable (fun q : (BitString × BitString) × BitString =>
        (body q.1.1).drop (split q.1.1)) :=
    Primrec.list_drop.to_comp.comp
      (hSplit.comp (Computable.fst.comp Computable.fst))
      (hBody.comp (Computable.fst.comp Computable.fst))
  have hSecondDrop :
      Computable (fun q : (BitString × BitString) × BitString =>
        q.1.2.length - suffixLength q.1.1) :=
    Primrec.nat_sub.to_comp.comp
      (Computable.list_length.comp
        (Computable.snd.comp Computable.fst))
      (hSuffixLength.comp (Computable.fst.comp Computable.fst))
  have hSecondContext :
      Computable (fun q : (BitString × BitString) × BitString =>
        q.1.2.drop (q.1.2.length - suffixLength q.1.1)) :=
    Primrec.list_drop.to_comp.comp
      hSecondDrop (Computable.snd.comp Computable.fst)
  have hSecondRun :
      Partrec (fun q : (BitString × BitString) × BitString =>
        V ((body q.1.1).drop (split q.1.1),
          q.1.2.drop (q.1.2.length - suffixLength q.1.1))) :=
    Partrec.comp hV.1 (hSecondProgram.pair hSecondContext)
  have hPair :
      Computable
        (fun q : ((BitString × BitString) × BitString) × BitString =>
          pairCode q.1.2 q.2) :=
    (show Computable₂ (fun a b : BitString => pairCode a b) from
      pairCode_computable).comp
        (Computable.snd.comp Computable.fst) Computable.snd
  have hSecond :
      Partrec (fun q : (BitString × BitString) × BitString =>
        (V ((body q.1.1).drop (split q.1.1),
          q.1.2.drop (q.1.2.length - suffixLength q.1.1))).map fun y =>
            pairCode q.2 y) :=
    Partrec.map hSecondRun hPair
  have hD : isDecompressor D := Partrec.bind hFirst hSecond
  obtain ⟨cD, hcD⟩ := hV.2 D hD
  refine ⟨cD + 7,
    fun u x y lx ly a b hlx hly ha hx hy => ?_⟩
  obtain ⟨px, hpxLength, hpx⟩ :=
    (condKLeIff V x (u.take lx) a).mp hx
  obtain ⟨py, hpyLength, hpy⟩ :=
    (condKLeIff V y (u.drop (u.length - ly)) b).mp hy
  set prog : BitString :=
    pairCode (Nat.bits px.length)
      (pairCode (Nat.bits lx)
        (pairCode (Nat.bits ly) (px ++ py))) with hProg
  have hDProd : produces D prog u (pairCode x y) := by
    change pairCode x y ∈
      (V ((body prog).take (split prog),
        u.take (prefixLength prog))).bind fun x =>
          (V ((body prog).drop (split prog),
            u.drop (u.length - suffixLength prog))).map fun y =>
              pairCode x y
    rw [hProg]
    simp only [body, split, prefixLength, suffixLength,
      decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits,
      List.take_left, List.drop_left]
    exact Part.mem_bind_iff.mpr
      ⟨x, hpx, Part.mem_map (fun z => pairCode x z) hpy⟩
  have hDBound :
      condK V (pairCode x y) u ≤
        (prog.length : ENat) + (cD : ENat) := by
    calc
      condK V (pairCode x y) u
          ≤ condK D (pairCode x y) u + (cD : ENat) :=
        hcD (pairCode x y) u
      _ ≤ (prog.length : ENat) + (cD : ENat) := by
        gcongr
        exact sInf_le ⟨prog, hDProd, rfl⟩
  have hBitsProgram :
      (Nat.bits px.length).length ≤ (Nat.bits a).length :=
    length_natBits_mono hpxLength
  have hBitsA :
      (Nat.bits a).length ≤
        (Nat.bits (u.length + 1)).length :=
    length_natBits_mono (by omega)
  have hBitsLx :
      (Nat.bits lx).length ≤
        (Nat.bits (u.length + 1)).length :=
    length_natBits_mono (by omega)
  have hBitsLy :
      (Nat.bits ly).length ≤
        (Nat.bits (u.length + 1)).length :=
    length_natBits_mono (by omega)
  have hProgLength :
      prog.length =
        2 * (Nat.bits px.length).length +
        2 * (Nat.bits lx).length +
        2 * (Nat.bits ly).length + 3 +
        px.length + py.length := by
    rw [hProg, length_pairCode, length_pairCode, length_pairCode,
      List.length_append]
    omega
  have hLength :
      prog.length + cD ≤
        a + b + logSlack (cD + 7) (u.length + 1) := by
    unfold logSlack
    rw [hProgLength]
    nlinarith
  exact hDBound.trans (by
    rw [← Nat.cast_add]
    exact_mod_cast hLength)

/-- **Visible-budget pair decoder.**  Same as `condK_pair_from_prefix_suffix_le`
but *without* the side condition `a ≤ u.length` on the first conditional budget.
The two decoded programs are packaged with `pairCode` (self-delimiting), so only
the two slice lengths `lx, ly` need explicit binary indices; the first program's
length is carried in unary by `pairCode`, costing `2·|px|` instead of a separate
`log` index.  The resulting budget is `2·a + b + O(log |u|)`.  This variant is
needed for the normalization step, where the resized-decoder budgets `a, b` are
`O(d + log |u|)` and may exceed `|u|` when `d` is large. -/
theorem condK_pair_from_prefix_suffix_visible_le
    (V : Map) (hV : isOptimalConditional V) :
  ∃ C, ∀ (u x y : BitString) (lx ly a b : Nat),
    lx ≤ u.length → ly ≤ u.length →
    condK V x (u.take lx) ≤ (a : ENat) →
    condK V y (u.drop (u.length - ly)) ≤ (b : ENat) →
    condK V (pairCode x y) u ≤
      (2 * a + b + logSlack C (u.length + 1) : ENat) := by
  -- Program layout: pairCode (bits lx) (pairCode (bits ly) (pairCode px py)).
  let progBody : BitString → BitString := fun q =>
    decodeSecond (decodeSecond q)
  let firstProg : BitString → BitString := fun q =>
    decodeFirst (progBody q)
  let secondProg : BitString → BitString := fun q =>
    decodeSecond (progBody q)
  let prefixLength : BitString → Nat := fun q =>
    decodeBits (decodeFirst q)
  let suffixLength : BitString → Nat := fun q =>
    decodeBits (decodeFirst (decodeSecond q))
  let D : Map := fun pr =>
    (V (firstProg pr.1, pr.2.take (prefixLength pr.1))).bind fun xx =>
      (V (secondProg pr.1,
          pr.2.drop (pr.2.length - suffixLength pr.1))).map fun yy =>
        pairCode xx yy
  have hProgBody : Computable progBody :=
    decodeSecond_computable.comp decodeSecond_computable
  have hFirstProg : Computable firstProg :=
    decodeFirst_computable.comp hProgBody
  have hSecondProg : Computable secondProg :=
    decodeSecond_computable.comp hProgBody
  have hPrefixLength : Computable prefixLength :=
    decodeBitsComputable.comp decodeFirst_computable
  have hSuffixLength : Computable suffixLength :=
    decodeBitsComputable.comp
      (decodeFirst_computable.comp decodeSecond_computable)
  have hFirstProgram : Computable (fun pr : BitString × BitString =>
      firstProg pr.1) := hFirstProg.comp Computable.fst
  have hFirstContext : Computable (fun pr : BitString × BitString =>
      pr.2.take (prefixLength pr.1)) :=
    Primrec.list_take.to_comp.comp (hPrefixLength.comp Computable.fst)
      Computable.snd
  have hFirst : Partrec (fun pr : BitString × BitString =>
      V (firstProg pr.1, pr.2.take (prefixLength pr.1))) :=
    Partrec.comp hV.1 (hFirstProgram.pair hFirstContext)
  have hSecondProgram :
      Computable (fun q : (BitString × BitString) × BitString =>
        secondProg q.1.1) :=
    hSecondProg.comp (Computable.fst.comp Computable.fst)
  have hSecondDrop :
      Computable (fun q : (BitString × BitString) × BitString =>
        q.1.2.length - suffixLength q.1.1) :=
    Primrec.nat_sub.to_comp.comp
      (Computable.list_length.comp
        (Computable.snd.comp Computable.fst))
      (hSuffixLength.comp (Computable.fst.comp Computable.fst))
  have hSecondContext :
      Computable (fun q : (BitString × BitString) × BitString =>
        q.1.2.drop (q.1.2.length - suffixLength q.1.1)) :=
    Primrec.list_drop.to_comp.comp
      hSecondDrop (Computable.snd.comp Computable.fst)
  have hSecondRun :
      Partrec (fun q : (BitString × BitString) × BitString =>
        V (secondProg q.1.1,
          q.1.2.drop (q.1.2.length - suffixLength q.1.1))) :=
    Partrec.comp hV.1 (hSecondProgram.pair hSecondContext)
  have hPair :
      Computable
        (fun q : ((BitString × BitString) × BitString) × BitString =>
          pairCode q.1.2 q.2) :=
    (show Computable₂ (fun a b : BitString => pairCode a b) from
      pairCode_computable).comp
        (Computable.snd.comp Computable.fst) Computable.snd
  have hSecond :
      Partrec (fun q : (BitString × BitString) × BitString =>
        (V (secondProg q.1.1,
          q.1.2.drop (q.1.2.length - suffixLength q.1.1))).map fun y =>
            pairCode q.2 y) :=
    Partrec.map hSecondRun hPair
  have hD : isDecompressor D := Partrec.bind hFirst hSecond
  obtain ⟨cD, hcD⟩ := hV.2 D hD
  refine ⟨cD + 7, fun u x y lx ly a b hlx hly hx hy => ?_⟩
  obtain ⟨px, hpxLength, hpx⟩ :=
    (condKLeIff V x (u.take lx) a).mp hx
  obtain ⟨py, hpyLength, hpy⟩ :=
    (condKLeIff V y (u.drop (u.length - ly)) b).mp hy
  set prog : BitString :=
    pairCode (Nat.bits lx)
      (pairCode (Nat.bits ly) (pairCode px py)) with hProg
  have hDProd : produces D prog u (pairCode x y) := by
    change pairCode x y ∈
      (V (firstProg prog, u.take (prefixLength prog))).bind fun xx =>
        (V (secondProg prog,
          u.drop (u.length - suffixLength prog))).map fun yy =>
            pairCode xx yy
    rw [hProg]
    simp only [firstProg, secondProg, progBody, prefixLength, suffixLength,
      decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]
    exact Part.mem_bind_iff.mpr
      ⟨x, hpx, Part.mem_map (fun z => pairCode x z) hpy⟩
  have hDBound :
      condK V (pairCode x y) u ≤
        (prog.length : ENat) + (cD : ENat) := by
    calc
      condK V (pairCode x y) u
          ≤ condK D (pairCode x y) u + (cD : ENat) :=
        hcD (pairCode x y) u
      _ ≤ (prog.length : ENat) + (cD : ENat) := by
        gcongr
        exact sInf_le ⟨prog, hDProd, rfl⟩
  have hBitsLx :
      (Nat.bits lx).length ≤ (Nat.bits (u.length + 1)).length :=
    length_natBits_mono (by omega)
  have hBitsLy :
      (Nat.bits ly).length ≤ (Nat.bits (u.length + 1)).length :=
    length_natBits_mono (by omega)
  have hProgLength :
      prog.length =
        2 * (Nat.bits lx).length +
        2 * (Nat.bits ly).length +
        2 * px.length + py.length + 3 := by
    rw [hProg, length_pairCode, length_pairCode, length_pairCode]
    omega
  have hLength :
      prog.length + cD ≤
        2 * a + b + logSlack (cD + 7) (u.length + 1) := by
    unfold logSlack
    rw [hProgLength]
    nlinarith
  exact hDBound.trans (by
    rw [← Nat.cast_add]
    exact_mod_cast hLength)


theorem condK_output_given_resized_reverseConcat_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C, ∀ a p z x na np r,
      produces V p [] z →
      produces V a z x →
      NatCloseWithin a.length na r →
      NatCloseWithin p.length np r →
      condK V x
        (resizeToLength a na ++ resizeToLength p np) ≤
      (commonInformationSlack C r
        (a.length + p.length + na + np + 1) : ENat) := by
  -- The program contains three binary indices (`na`, `|a|`, `|p|`) and
  -- the two literal suffixes discarded by resizing.  The condition determines
  -- the resized blocks because its left block has the advertised exact length
  -- `na`.
  let splitLength : BitString → Nat := fun q =>
    decodeBits (decodeFirst q)
  let firstLength : BitString → Nat := fun q =>
    decodeBits (decodeFirst (decodeSecond q))
  let secondLength : BitString → Nat := fun q =>
    decodeBits (decodeFirst (decodeSecond (decodeSecond q)))
  let tails : BitString → BitString := fun q =>
    decodeSecond (decodeSecond (decodeSecond q))
  let firstTail : BitString → BitString := fun q =>
    decodeFirst (tails q)
  let secondTail : BitString → BitString := fun q =>
    decodeSecond (tails q)
  let restoreFirst : BitString × BitString → BitString := fun pr =>
    (pr.2.take (splitLength pr.1)).take (firstLength pr.1) ++
      firstTail pr.1
  let restoreSecond : BitString × BitString → BitString := fun pr =>
    (pr.2.drop (splitLength pr.1)).take (secondLength pr.1) ++
      secondTail pr.1
  let D : Map := fun pr =>
    (V (restoreSecond pr, [])).bind fun z =>
      V (restoreFirst pr, z)
  have hSplitLength : Computable splitLength :=
    decodeBitsComputable.comp decodeFirst_computable
  have hFirstLength : Computable firstLength :=
    decodeBitsComputable.comp
      (decodeFirst_computable.comp decodeSecond_computable)
  have hSecondLength : Computable secondLength :=
    decodeBitsComputable.comp
      (decodeFirst_computable.comp
        (decodeSecond_computable.comp decodeSecond_computable))
  have hTails : Computable tails :=
    decodeSecond_computable.comp
      (decodeSecond_computable.comp decodeSecond_computable)
  have hFirstTail : Computable firstTail :=
    decodeFirst_computable.comp hTails
  have hSecondTail : Computable secondTail :=
    decodeSecond_computable.comp hTails
  have hRestoreFirst : Computable restoreFirst := by
    exact Computable.list_append.comp
      (Primrec.list_take.to_comp.comp
        (hFirstLength.comp Computable.fst)
        (Primrec.list_take.to_comp.comp (hSplitLength.comp Computable.fst)
          Computable.snd))
      (hFirstTail.comp Computable.fst)
  have hRestoreSecond : Computable restoreSecond := by
    exact Computable.list_append.comp
      (Primrec.list_take.to_comp.comp
        (hSecondLength.comp Computable.fst)
        (Primrec.list_drop.to_comp.comp (hSplitLength.comp Computable.fst)
          Computable.snd))
      (hSecondTail.comp Computable.fst)
  have hFirstRun : Partrec (fun pr : BitString × BitString =>
      V (restoreSecond pr, [])) :=
    Partrec.comp hV.1
      (hRestoreSecond.pair (Computable.const []))
  have hSecondRun :
      Partrec (fun q : (BitString × BitString) × BitString =>
        V (restoreFirst q.1, q.2)) :=
    Partrec.comp hV.1
      ((hRestoreFirst.comp Computable.fst).pair Computable.snd)
  have hD : isDecompressor D := Partrec.bind hFirstRun hSecondRun
  obtain ⟨cD, hcD⟩ := hV.2 D hD
  let C := cD + 10
  refine ⟨C, fun a p z x na np r hp ha hna hnp => ?_⟩
  set prog : BitString :=
    pairCode (Nat.bits na)
      (pairCode (Nat.bits a.length)
        (pairCode (Nat.bits p.length)
          (pairCode (a.drop na) (p.drop np)))) with hProg
  set ctx : BitString :=
    resizeToLength a na ++ resizeToLength p np with hCtx
  have hTakeCtx : ctx.take na = resizeToLength a na := by
    rw [hCtx]
    simp
  have hDropCtx : ctx.drop na = resizeToLength p np := by
    rw [hCtx]
    simp
  have hRestoreFirstEval : restoreFirst (prog, ctx) = a := by
    dsimp [restoreFirst, splitLength, firstLength, firstTail, tails]
    rw [hProg]
    simp only [decodeFirst_pairCode, decodeSecond_pairCode,
      decodeBits_natBits, hTakeCtx]
    exact resizeToLength_take_original_append_drop a na
  have hRestoreSecondEval : restoreSecond (prog, ctx) = p := by
    dsimp [restoreSecond, splitLength, secondLength, secondTail, tails]
    rw [hProg]
    simp only [decodeFirst_pairCode, decodeSecond_pairCode,
      decodeBits_natBits, hDropCtx]
    exact resizeToLength_take_original_append_drop p np
  have hDProd : produces D prog ctx x := by
    change x ∈ (V (restoreSecond (prog, ctx), [])).bind
      (fun z => V (restoreFirst (prog, ctx), z))
    rw [hRestoreFirstEval, hRestoreSecondEval]
    exact Part.mem_bind_iff.mpr ⟨z, hp, ha⟩
  have hDBound :
      condK V x ctx ≤ (prog.length : ENat) + (cD : ENat) := by
    calc
      condK V x ctx ≤ condK D x ctx + (cD : ENat) := hcD x ctx
      _ ≤ (prog.length : ENat) + (cD : ENat) := by
        gcongr
        exact sInf_le ⟨prog, hDProd, rfl⟩
  have hDropA : (a.drop na).length ≤ r := by
    rw [List.length_drop]
    unfold NatCloseWithin at hna
    omega
  have hDropP : (p.drop np).length ≤ r := by
    rw [List.length_drop]
    unfold NatCloseWithin at hnp
    omega
  let N := a.length + p.length + na + np + 1
  have hBitsNa :
      (Nat.bits na).length ≤ (Nat.bits N).length :=
    length_natBits_mono (by dsimp [N]; omega)
  have hBitsA :
      (Nat.bits a.length).length ≤ (Nat.bits N).length :=
    length_natBits_mono (by dsimp [N]; omega)
  have hBitsP :
      (Nat.bits p.length).length ≤ (Nat.bits N).length :=
    length_natBits_mono (by dsimp [N]; omega)
  have hProgLength :
      prog.length =
        2 * (Nat.bits na).length +
        2 * (Nat.bits a.length).length +
        2 * (Nat.bits p.length).length +
        2 * (a.drop na).length + (p.drop np).length + 4 := by
    rw [hProg, length_pairCode, length_pairCode, length_pairCode,
      length_pairCode]
    omega
  have hLength :
      prog.length + cD ≤ commonInformationSlack C r N := by
    unfold commonInformationSlack logSlack
    rw [hProgLength]
    dsimp [C]
    nlinarith
  rw [hCtx] at hDBound
  exact hDBound.trans (by
    rw [← Nat.cast_add]
    exact_mod_cast hLength)

theorem condK_output_given_resized_forwardConcat_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C, ∀ p b z y np nb r,
      produces V p [] z →
      produces V b z y →
      NatCloseWithin p.length np r →
      NatCloseWithin b.length nb r →
      condK V y
        (resizeToLength p np ++ resizeToLength b nb) ≤
      (commonInformationSlack C r
        (p.length + b.length + np + nb + 1) : ENat) := by
  let splitLength : BitString → Nat := fun q =>
    decodeBits (decodeFirst q)
  let firstLength : BitString → Nat := fun q =>
    decodeBits (decodeFirst (decodeSecond q))
  let secondLength : BitString → Nat := fun q =>
    decodeBits (decodeFirst (decodeSecond (decodeSecond q)))
  let tails : BitString → BitString := fun q =>
    decodeSecond (decodeSecond (decodeSecond q))
  let firstTail : BitString → BitString := fun q =>
    decodeFirst (tails q)
  let secondTail : BitString → BitString := fun q =>
    decodeSecond (tails q)
  let restoreFirst : BitString × BitString → BitString := fun pr =>
    (pr.2.take (splitLength pr.1)).take (firstLength pr.1) ++
      firstTail pr.1
  let restoreSecond : BitString × BitString → BitString := fun pr =>
    (pr.2.drop (splitLength pr.1)).take (secondLength pr.1) ++
      secondTail pr.1
  let D : Map := fun pr =>
    (V (restoreFirst pr, [])).bind fun z =>
      V (restoreSecond pr, z)
  have hSplitLength : Computable splitLength :=
    decodeBitsComputable.comp decodeFirst_computable
  have hFirstLength : Computable firstLength :=
    decodeBitsComputable.comp
      (decodeFirst_computable.comp decodeSecond_computable)
  have hSecondLength : Computable secondLength :=
    decodeBitsComputable.comp
      (decodeFirst_computable.comp
        (decodeSecond_computable.comp decodeSecond_computable))
  have hTails : Computable tails :=
    decodeSecond_computable.comp
      (decodeSecond_computable.comp decodeSecond_computable)
  have hFirstTail : Computable firstTail :=
    decodeFirst_computable.comp hTails
  have hSecondTail : Computable secondTail :=
    decodeSecond_computable.comp hTails
  have hRestoreFirst : Computable restoreFirst := by
    exact Computable.list_append.comp
      (Primrec.list_take.to_comp.comp
        (hFirstLength.comp Computable.fst)
        (Primrec.list_take.to_comp.comp (hSplitLength.comp Computable.fst)
          Computable.snd))
      (hFirstTail.comp Computable.fst)
  have hRestoreSecond : Computable restoreSecond := by
    exact Computable.list_append.comp
      (Primrec.list_take.to_comp.comp
        (hSecondLength.comp Computable.fst)
        (Primrec.list_drop.to_comp.comp (hSplitLength.comp Computable.fst)
          Computable.snd))
      (hSecondTail.comp Computable.fst)
  have hFirstRun : Partrec (fun pr : BitString × BitString =>
      V (restoreFirst pr, [])) :=
    Partrec.comp hV.1
      (hRestoreFirst.pair (Computable.const []))
  have hSecondRun :
      Partrec (fun q : (BitString × BitString) × BitString =>
        V (restoreSecond q.1, q.2)) :=
    Partrec.comp hV.1
      ((hRestoreSecond.comp Computable.fst).pair Computable.snd)
  have hD : isDecompressor D := Partrec.bind hFirstRun hSecondRun
  obtain ⟨cD, hcD⟩ := hV.2 D hD
  let C := cD + 10
  refine ⟨C, fun p b z y np nb r hp hb hnp hnb => ?_⟩
  set prog : BitString :=
    pairCode (Nat.bits np)
      (pairCode (Nat.bits p.length)
        (pairCode (Nat.bits b.length)
          (pairCode (p.drop np) (b.drop nb)))) with hProg
  set ctx : BitString :=
    resizeToLength p np ++ resizeToLength b nb with hCtx
  have hTakeCtx : ctx.take np = resizeToLength p np := by
    rw [hCtx]
    simp
  have hDropCtx : ctx.drop np = resizeToLength b nb := by
    rw [hCtx]
    simp
  have hRestoreFirstEval : restoreFirst (prog, ctx) = p := by
    dsimp [restoreFirst, splitLength, firstLength, firstTail, tails]
    rw [hProg]
    simp only [decodeFirst_pairCode, decodeSecond_pairCode,
      decodeBits_natBits, hTakeCtx]
    exact resizeToLength_take_original_append_drop p np
  have hRestoreSecondEval : restoreSecond (prog, ctx) = b := by
    dsimp [restoreSecond, splitLength, secondLength, secondTail, tails]
    rw [hProg]
    simp only [decodeFirst_pairCode, decodeSecond_pairCode,
      decodeBits_natBits, hDropCtx]
    exact resizeToLength_take_original_append_drop b nb
  have hDProd : produces D prog ctx y := by
    change y ∈ (V (restoreFirst (prog, ctx), [])).bind
      (fun z => V (restoreSecond (prog, ctx), z))
    rw [hRestoreFirstEval, hRestoreSecondEval]
    exact Part.mem_bind_iff.mpr ⟨z, hp, hb⟩
  have hDBound :
      condK V y ctx ≤ (prog.length : ENat) + (cD : ENat) := by
    calc
      condK V y ctx ≤ condK D y ctx + (cD : ENat) := hcD y ctx
      _ ≤ (prog.length : ENat) + (cD : ENat) := by
        gcongr
        exact sInf_le ⟨prog, hDProd, rfl⟩
  have hDropP : (p.drop np).length ≤ r := by
    rw [List.length_drop]
    unfold NatCloseWithin at hnp
    omega
  have hDropB : (b.drop nb).length ≤ r := by
    rw [List.length_drop]
    unfold NatCloseWithin at hnb
    omega
  let N := p.length + b.length + np + nb + 1
  have hBitsNp :
      (Nat.bits np).length ≤ (Nat.bits N).length :=
    length_natBits_mono (by dsimp [N]; omega)
  have hBitsP :
      (Nat.bits p.length).length ≤ (Nat.bits N).length :=
    length_natBits_mono (by dsimp [N]; omega)
  have hBitsB :
      (Nat.bits b.length).length ≤ (Nat.bits N).length :=
    length_natBits_mono (by dsimp [N]; omega)
  have hProgLength :
      prog.length =
        2 * (Nat.bits np).length +
        2 * (Nat.bits p.length).length +
        2 * (Nat.bits b.length).length +
        2 * (p.drop np).length + (b.drop nb).length + 4 := by
    rw [hProg, length_pairCode, length_pairCode, length_pairCode,
      length_pairCode]
    omega
  have hLength :
      prog.length + cD ≤ commonInformationSlack C r N := by
    unfold commonInformationSlack logSlack
    rw [hProgLength]
    dsimp [C]
    nlinarith
  rw [hCtx] at hDBound
  exact hDBound.trans (by
    rw [← Nat.cast_add]
    exact_mod_cast hLength)

end Kolmogorov
