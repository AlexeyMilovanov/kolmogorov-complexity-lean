import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainProfile

/-!
# Bridges between ordinary plain and prefix description profiles
-/

namespace Kolmogorov

/-- An ordinary plain description can be viewed as a prefix description after
adding logarithmic overhead to the model-complexity coordinate. -/
theorem inDescriptionProfile_of_inPlainDescriptionProfile
    (V U : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c, ∀ x i j,
      InPlainDescriptionProfile V x i j →
      InDescriptionProfile U x (i + logSlack c i) j := by
  -- Get the bridge from plainK to KPPlain with log overhead
  obtain ⟨c1, hc1⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  -- Get a bound on KPPlain U for any bitstring in terms of its length
  obtain ⟨c2, hc2_len⟩ := KPPlain_le_two_mul_length U hU
  -- Use an additive constant that's large enough
  use c1 + c2 + 2
  intro x i j hprofile
  -- Extract the set S from the plain description profile
  obtain ⟨S, hS, hxS, hScomp, hScard⟩ := hprofile
  -- We need to show InDescriptionProfile U x (i + logSlack (c1 + c2 + 2) i) j
  refine ⟨S, hS, ⟨hxS, ?_, hScard⟩⟩
  -- setComplexity U S hS = KPPlain U (codedUniformOn S hS).code
  unfold setComplexity
  -- plainK V (codedUniformOn S hS).code ≤ i
  have hplainK_le_i := hScomp
  -- We need KPPlain U p ≤ i + logSlack (c1 + c2 + 2) i
  -- Apply hc1 to get KPPlain U p ≤ plainK V p + KPPlain U (Nat.bits kC) + c1
  let p := (codedUniformOn S hS).code
  have key : KPPlain U p ≤ (i : ENat) + logSlack (c1 + c2 + 2) i := by
    -- We have plainK V p ≤ i (from hplainK_le_i which comes from hScomp)
    -- Since i is finite, plainK V p ≠ ⊤, so plainK V p = kC for some kC ≤ i.
    -- plainSetComplexity V S hS = plainK V p
    have hp_eq : plainSetComplexity V S hS = plainK V p := rfl
    have hplainK_le_i' : plainK V p ≤ (i : ENat) := hp_eq ▸ hplainK_le_i
    have hfi : plainK V p ≠ ⊤ := fun h => by simp [h] at hplainK_le_i'
    obtain ⟨kC, hkC⟩ : ∃ kC : ℕ, plainK V p = (kC : ENat) :=
      (ENat.ne_top_iff_exists.mp hfi).imp fun m hm => hm.symm
    have hkC_le_i : kC ≤ i := by
      rw [hkC] at hplainK_le_i'
      exact_mod_cast hplainK_le_i'
    -- Apply hc1
    have h1 := hc1 p kC hkC
    -- Apply hc2_len to bound KPPlain U (Nat.bits kC)
    have h2 := hc2_len (Nat.bits kC)
    -- Nat.size n = (Nat.bits n).length
    have hsize_le : (Nat.bits kC).length ≤ (Nat.bits i).length := by
      rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
      exact Nat.size_le_size hkC_le_i
    -- Combine
    have step2 : KPPlain U p ≤
        (kC : ENat) + (2 * (Nat.bits kC).length + (c2 : ENat)) +
          (c1 : ENat) := by
      calc KPPlain U p ≤ (kC : ENat) + KPPlain U (Nat.bits kC) + (c1 : ENat) := h1
        _ ≤ (kC : ENat) + (2 * (Nat.bits kC).length + (c2 : ENat)) +
            (c1 : ENat) := by gcongr
    have step3 : KPPlain U p ≤ (kC : ENat) + 2 * (Nat.bits kC).length + (c1 + c2 : ENat) := by
      convert step2 using 1
      simp [add_assoc, add_comm, add_left_comm]
    have step4 : KPPlain U p ≤ (i : ENat) + 2 * (Nat.bits i).length + (c1 + c2 : ENat) := by
      calc KPPlain U p ≤ (kC : ENat) + 2 * (Nat.bits kC).length + (c1 + c2 : ENat) := step3
        _ ≤ (i : ENat) + 2 * (Nat.bits i).length + (c1 + c2 : ENat) := by gcongr
    have step5 : KPPlain U p ≤ (i : ENat) + logSlack (c1 + c2 + 2) i := by
      simp only [logSlack]
      calc KPPlain U p ≤ (i : ENat) + 2 * (Nat.bits i).length + (c1 + c2 : ENat) := step4
        _ ≤ (i : ENat) + ((c1 + c2 + 2) * (Nat.bits i).length + (c1 + c2 + 2)) := by
          have h : 2 * (Nat.bits i).length + (c1 + c2 : ℕ) ≤
                   (c1 + c2 + 2) * (Nat.bits i).length + (c1 + c2 + 2) := by nlinarith
          have h' : (i : ℕ) + 2 * (Nat.bits i).length + (c1 + c2) ≤
                    (i : ℕ) + ((c1 + c2 + 2) * (Nat.bits i).length + (c1 + c2 + 2)) := by omega
          exact_mod_cast h'
    exact step5
  exact key

/-- Membership in the ordinary plain two-part profile yields the expected
plain two-part coding bound for the described string.  The prefix-optimality
hypothesis is retained for the source-facing interface, although the direct plain
decoder proof does not need it. -/
theorem plainK_le_of_inPlainDescriptionProfile
    (V U : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
  ∃ c : Nat, ∀ (x : BitString) (n i j : Nat),
    x.length = n →
    InPlainDescriptionProfile V x i j →
    plainK V x ≤
      (i + j + logSlack c (n + i + j) : ENat) := by
  have _hU := hU
  -- Define a decompressor that decodes x from totalProgramPairCode p_S (Nat.bits u)
  -- where p_S is a program that produces code_S = (codedUniformOn S hS).code,
  -- and Nat.bits u is the binary encoding of u (the ordinal of x in S)
  let myDecompressor : Map := fun (pr : BitString × BitString) =>
    -- Run the program to get code_S, then decode
    let p := decodeTotalProgramPairFirst pr.1
    Part.bind (V (p, [])) (fun code_S =>
      Part.some ((canonicalPointListOfCode code_S).getD
        (decodeBits (decodeTotalProgramPairSecond pr.1)) []))
  have hmyDecompressor_partrec : isDecompressor myDecompressor := by
    -- Need to show Partrec myDecompressor
    -- myDecompressor = fun pr => (V (pr.1, [])).bind (fun code_S => some (...))
    have hV : Partrec V := hV.1
    have hV_cond : Partrec (fun (pr : BitString × BitString) =>
        V (decodeTotalProgramPairFirst pr.1, [])) := by
      apply Partrec.comp hV
      exact (Computable.pair
        (decodeTotalProgramPairFirst_computable.comp Computable.fst)
        (Computable.const [])).to₂
    haveI : Primcodable (Part BitString) := by
      classical
      exact Primcodable.ofEquiv _ {
        toFun := fun p => if h : p.Dom then some (p.get h) else none
        invFun := Part.ofOption
        left_inv := fun p => Part.ext_iff.mpr fun x => by
          by_cases h : p.Dom <;> simp_all [Part.dom_iff_mem]
        right_inv := fun o => by
          cases o with
          | none => simp
          | some val => simp
      }
    have hpost : Partrec₂ (fun (pr : BitString × BitString) (code_S : BitString) =>
        Part.some ((canonicalPointListOfCode code_S).getD
          (decodeBits (decodeTotalProgramPairSecond pr.1)) [])) := by
      have hinner : Computable₂ (fun (pr : BitString × BitString) (code_S : BitString) =>
          some ((canonicalPointListOfCode code_S).getD
            (decodeBits (decodeTotalProgramPairSecond pr.1)) [])) := by
        simp only [Computable₂]
        have decodeIdx : Computable (fun p : ((BitString × BitString) × BitString) =>
            decodeBits (decodeTotalProgramPairSecond p.1.1)) :=
          primrecDecodeBits.to_comp.comp
            (decodeTotalProgramPairSecond_computable.comp (Computable.fst.comp Computable.fst))
        have listCode : Computable (fun p : ((BitString × BitString) × BitString) =>
            canonicalPointListOfCode p.2) :=
          canonicalPointListOfCode_primrec.to_comp.comp Computable.snd
        have hgetD : Computable (fun p : ((BitString × BitString) × BitString) =>
            (canonicalPointListOfCode p.2).getD
              (decodeBits (decodeTotalProgramPairSecond p.1.1)) []) :=
          (Primrec.list_getD ([] : BitString)).to_comp.comp listCode decodeIdx
        exact Computable.option_some.comp hgetD
      exact Computable.ofOption hinner
    exact Partrec.bind hV_cond hpost
  -- Get the constant from optimality of V
  obtain ⟨c', hc'⟩ := hV.2 myDecompressor hmyDecompressor_partrec
  -- Choose c large enough to absorb c' into logSlack
  use c' + 2
  intro x n i j hxlen hprofile
  obtain ⟨S, hS, hxS, hScomp, hScard⟩ := hprofile
  -- Get the ordinal of x in S
  let l := canonicalFinsetList S
  have hx_in_l : x ∈ l := mem_canonicalFinsetList.mpr hxS
  let u := l.findIdx (fun w => decide (w = x))
  have hu_lt_card : u < S.card := by
    have hlt : u < l.length := List.findIdx_lt_length.mpr ⟨x, hx_in_l, by simp⟩
    rwa [length_canonicalFinsetList] at hlt
  have hu_lt_2j : u < 2^j := hu_lt_card.trans_le hScard
  let code_S := (codedUniformOn S hS).code
  -- plainK V code_S ≤ i means there's a program of length ≤ i that produces code_S
  have hcodeS_comp : plainK V code_S ≤ (i : ENat) := hScomp
  -- Get a concrete program for code_S with length ≤ i
  obtain ⟨p_S, hpS_len, hpS_prod⟩ :
      ∃ p_S, programLength p_S ≤ i ∧ produces V p_S [] code_S :=
    condKLeIff V code_S [] i |>.mp hcodeS_comp
  -- Use Nat.bits for the index (length ≈ log u ≤ log(2^j) = j)
  let uCode := Nat.bits u
  have huCode_len : uCode.length ≤ j := by
    simp only [uCode]
    by_cases hu_zero : u = 0
    · simp [hu_zero]
    · have hlog : Nat.log 2 u < j := Nat.log_lt_of_lt_pow hu_zero hu_lt_2j
      have hbits : (Nat.bits u).length ≤ j := by
        have h1 := (@Nat.size_le u j).mpr hu_lt_2j
        simpa [← Nat.size_eq_bits_len] using h1
      omega
  have huCode_decode : decodeBits uCode = u := decodeBits_natBits u
  -- Define the full program as totalProgramPairCode p_S uCode
  let prog := totalProgramPairCode p_S uCode
  -- Show that prog produces x on myDecompressor
  have hprod : produces myDecompressor prog [] x := by
    unfold produces myDecompressor
    rw [Part.mem_bind_iff]
    refine ⟨code_S, ?_, ?_⟩
    · rw [decodeTotalProgramPairFirst_pair]
      exact hpS_prod
    · simp only [Part.mem_some_iff]
      rw [decodeTotalProgramPairSecond_pair, huCode_decode]
      rw [canonicalPointListOfCode_codedUniformOn]
      have hlt :
          (canonicalFinsetList S).findIdx (fun w => decide (w = x)) <
            (canonicalFinsetList S).length := by
        rw [List.findIdx_lt_length]
        exact ⟨x, mem_canonicalFinsetList.mpr hxS, by simp⟩
      rw [List.getD_eq_getElem (canonicalFinsetList S) [] hlt]
      have hge := List.findIdx_getElem (p := fun w => decide (w = x)) (w := hlt)
      rw [decide_eq_true_eq] at hge
      exact hge.symm
  -- Bound the length of prog
  have hprog_len :
      prog.length =
        p_S.length + uCode.length + 2 * (Nat.bits p_S.length).length + 1 :=
    length_totalProgramPairCode p_S uCode
  -- Now use optimality of V
  calc plainK V x
      ≤ condK myDecompressor x [] + (c' : ENat) := hc' x []
    _ ≤ (prog.length : ENat) + (c' : ENat) := by
        gcongr
        exact sInf_le ⟨prog, hprod, rfl⟩
    _ = (p_S.length + uCode.length + 2 * (Nat.bits p_S.length).length + 1 + c' : ENat) := by
        rw [hprog_len]
        simp
    _ ≤ (i + j + 2 * (Nat.bits (i + j)).length + 1 + c' : ENat) := by
        have hpS_le_ij : p_S.length ≤ i + j := Nat.le_trans hpS_len (Nat.le_add_right _ _)
        have hb3 : (Nat.bits p_S.length).length ≤ (Nat.bits (i + j)).length :=
          length_natBits_mono hpS_le_ij
        have h1 : (p_S.length + uCode.length + 2 * (Nat.bits p_S.length).length + 1 + c' : ℕ) ≤
                  (i + j + 2 * (Nat.bits (i + j)).length + 1 + c' : ℕ) := by
          have := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hpS_len huCode_len)
            (Nat.mul_le_mul_left 2 hb3)) (le_refl 1)) (le_refl c')
          linarith
        exact_mod_cast h1
    _ ≤ (i + j + logSlack (c' + 2) (n + i + j) : ENat) := by
        simp only [logSlack]
        have h1 : (Nat.bits (i + j)).length ≤ (Nat.bits (n + i + j)).length := by
          apply length_natBits_mono
          omega
        have hbits_ge : (Nat.bits (i + j)).length ≥ 0 := Nat.zero_le _
        have h2 : (i + j + 2 * (Nat.bits (i + j)).length + 1 + c' : ℕ) ≤
                  (i + j + ((c' + 2) * (Nat.bits (n + i + j)).length + (c' + 2)) : ℕ) := by
          have hmul : 2 * (Nat.bits (i + j)).length ≤ (c' + 2) * (Nat.bits (n + i + j)).length := by
            calc 2 * (Nat.bits (i + j)).length
                ≤ (c' + 2) * (Nat.bits (i + j)).length := Nat.mul_le_mul_right _ (by omega)
              _ ≤ (c' + 2) * (Nat.bits (n + i + j)).length := Nat.mul_le_mul_left _ h1
          linarith
        exact_mod_cast h2

/-- An ordinary prefix description can be viewed as a plain description with
a constant overhead in the model-complexity coordinate. -/
theorem inPlainDescriptionProfile_of_inDescriptionProfile
    (V U : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c, ∀ x i j,
      InDescriptionProfile U x i j →
      InPlainDescriptionProfile V x (i + c) j := by
  obtain ⟨c, hc⟩ := plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  refine ⟨c, fun x i j hprofile => ?_⟩
  obtain ⟨S, hS, hdesc⟩ := hprofile
  refine ⟨S, hS, hdesc.1, ?_, hdesc.2.2⟩
  unfold plainSetComplexity at *
  calc
    plainK V (codedUniformOn S hS).code
        ≤ KPPlain U (codedUniformOn S hS).code + (c : ENat) := hc _
    _ ≤ (i : ENat) + (c : ENat) := by
      gcongr
      simpa [setComplexity] using hdesc.2.1
    _ = ((i + c : Nat) : ENat) := by push_cast; rfl

end Kolmogorov
