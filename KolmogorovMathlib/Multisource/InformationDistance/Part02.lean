import KolmogorovMathlib.Multisource.InformationDistance.Part01

/-!
# Information distance and simultaneous encoding: Part 2
Theorems 232 and 233 prove sufficiency by colouring an enumerable bipartite graph.
The statements retain the produced off-by-one lengths. SUV Section 12.6, pp. 377–379.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
/-- Helper. -/
theorem exists_informationDistance_colouring (D : Map) (hD : Partrec D) :
    ∃ colour : ℕ → BitString → BitString →. BitString,
      IsInformationDistanceColouring D colour := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hD
  refine ⟨fun k A B => idcFind c 0 (k, k) (A, B), idcColour_partrec c,
    fun k A B hAB hBA => ?_⟩
  obtain ⟨s, X, hX⟩ := idcAssign_covers hc le_rfl (show idcGraph D (k, k) (A, B)
      from ⟨hAB, hBA⟩)
  have hm : X ∈ idcFind c 0 (k, k) (A, B) := idcFind_spec hX (by simp [idcMatch])
  refine ⟨X, hm, idcAssign_length hX, fun B' h => ?_, fun A' h => ?_⟩
  · exact (Prod.mk.inj (idcFind_zero_unique hm h (Or.inl rfl))).2.symm
  · exact (Prod.mk.inj (idcFind_zero_unique hm h (Or.inr rfl))).1.symm
section IdcDecompressor
open Nat.Partrec (Code)
/-- The colouring packaged as a `Map`: the program is `pairCode (bits k) u`, the condition is
the second endpoint `w`, and the output is `colour k u w`.  Used to recover the second endpoint. -/
def idcColourMap (colour : ℕ → BitString → BitString →. BitString) : Map := fun pr =>
  colour (bitsToNat (decodeFirst pr.1)) (decodeSecond pr.1) pr.2
/-- The swapped packaging: the condition ranges over the first endpoint while the second endpoint
is baked into the program.  Used to recover the first endpoint. -/
def idcColourMapSwap (colour : ℕ → BitString → BitString →. BitString) : Map := fun pr =>
  colour (bitsToNat (decodeFirst pr.1)) pr.2 (decodeSecond pr.1)
/-- Helper. -/
theorem idcColourMap_partrec (colour : ℕ → BitString → BitString →. BitString)
    (h : Partrec (fun q : (ℕ × BitString) × BitString => colour q.1.1 q.1.2 q.2)) :
    Partrec (idcColourMap colour) :=
  h.comp (Computable.pair (Computable.pair
    (bitsToNat_primrec.to_comp.comp (decodeFirst_computable.comp Computable.fst))
    (decodeSecond_computable.comp Computable.fst)) Computable.snd)
/-- Helper. -/
theorem idcColourMapSwap_partrec (colour : ℕ → BitString → BitString →. BitString)
    (h : Partrec (fun q : (ℕ × BitString) × BitString => colour q.1.1 q.1.2 q.2)) :
    Partrec (idcColourMapSwap colour) :=
  h.comp (Computable.pair (Computable.pair
    (bitsToNat_primrec.to_comp.comp (decodeFirst_computable.comp Computable.fst))
    Computable.snd) (decodeSecond_computable.comp Computable.fst))
/-- One probe of the dovetailing preimage search: decode `n` as `(step, w)` and keep `w` when
running the code on `(p, w)` for `step` steps outputs `v`. -/
def idcPreQuery (c : Code) (p v : BitString) (n : ℕ) : Option BitString :=
  (Encodable.decode (α := BitString) n.unpair.2).bind fun w =>
    bif decide (idcRun c n.unpair.1 p w = some v) then some w else none
/-- The dovetailing preimage search: find a condition `w` on which the code run on `(p, w)`
eventually outputs `v`, and return that `w`. -/
def idcPre (c : Code) (p v : BitString) : Part BitString :=
  (Nat.rfind fun n => Part.some (idcPreQuery c p v n).isSome).bind fun n =>
    Part.ofOption (idcPreQuery c p v n)
/-- Helper. -/
theorem idcPreQuery_primrec (c : Code) :
    Primrec (fun a : (BitString × BitString) × ℕ => idcPreQuery c a.1.1 a.1.2 a.2) := by
  unfold idcPreQuery
  have hbool : Primrec (fun x : ((BitString × BitString) × ℕ) × BitString =>
      decide (idcRun c x.1.2.unpair.1 x.1.1.1 x.2 = some x.1.1.2)) :=
    (PrimrecRel.decide Primrec.eq).comp
      ((idcRun_primrec c).comp (Primrec.pair
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)))
      (Primrec.option_some.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  exact Primrec.option_bind
    (Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
    (Primrec.cond hbool (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂
/-- Helper. -/
theorem idcPre_partrec (c : Code) :
    Partrec (fun a : BitString × BitString => idcPre c a.1 a.2) := by
  have h1 : Computable (fun a : (BitString × BitString) × ℕ =>
      idcPreQuery c a.1.1 a.1.2 a.2) := (idcPreQuery_primrec c).to_comp
  have h2 : Computable₂ (fun (a : BitString × BitString) (n : ℕ) =>
      (idcPreQuery c a.1 a.2 n).isSome) :=
    Primrec.option_isSome.to_comp.comp h1
  exact Partrec.bind (Partrec.rfind h2.partrec₂) (Computable.ofOption h1).to₂
/-- Helper. -/
theorem idcPre_mem {c : Code} {p v out : BitString}
    (h : out ∈ idcPre c p v) : ∃ s, idcRun c s p out = some v := by
  unfold idcPre at h
  rcases Part.mem_bind_iff.1 h with ⟨n, -, hn⟩
  rw [Part.mem_ofOption, Option.mem_def] at hn
  unfold idcPreQuery at hn
  rw [Option.bind_eq_some_iff] at hn
  obtain ⟨w, -, hb⟩ := hn
  cases hd : decide (idcRun c n.unpair.1 p w = some v) with
  | false => rw [hd, Bool.cond_false] at hb; exact absurd hb (by simp)
  | true =>
    rw [hd, Bool.cond_true, Option.some.injEq] at hb
    exact ⟨n.unpair.1, hb ▸ of_decide_eq_true hd⟩
/-- Helper. -/
theorem idcPre_spec {c : Code} {p v w0 : BitString} {s0 : ℕ}
    (h : idcRun c s0 p w0 = some v) : ∃ out, out ∈ idcPre c p v := by
  have hex : ∃ n, (idcPreQuery c p v n).isSome := by
    refine ⟨Nat.pair s0 (Encodable.encode w0), ?_⟩
    simp [idcPreQuery, Nat.unpair_pair, Encodable.encodek, h]
  obtain ⟨out, hout⟩ := Option.isSome_iff_exists.1 (Nat.find_spec hex)
  refine ⟨out, ?_⟩
  unfold idcPre
  rw [Part.mem_bind_iff]
  refine ⟨Nat.find hex, ?_, ?_⟩
  · exact Nat.mem_rfind.2
      ⟨by simpa using Nat.find_spec hex, fun {m} hm => by simpa using Nat.find_min hex hm⟩
  · rw [Part.mem_ofOption, Option.mem_def]
    exact hout
/-- Helper. -/
theorem idcPre_mem_unique {c : Code} {D : Map} (hc : IsCodeFor c D)
    {p v target : BitString} (hcomplete : v ∈ D (p, target))
    (huniq : ∀ w, v ∈ D (p, w) → w = target) : target ∈ idcPre c p v := by
  obtain ⟨s0, hs0⟩ := idcRun_complete hc hcomplete
  obtain ⟨out, hout⟩ := idcPre_spec hs0
  obtain ⟨s, hs⟩ := idcPre_mem hout
  rw [huniq out (idcRun_sound hc hs)] at hout
  exact hout
/-- The simultaneous decompressor `E`: the program decodes a mode and `k`, the condition decodes
two strings, and the three modes return the colour, the recovered second endpoint, and the
recovered first endpoint. -/
def idcDecomp (colour : ℕ → BitString → BitString →. BitString) (c c' : Code) : Map :=
  fun pr =>
    bif decide (bitsToNat (decodeFirst pr.1) = 0)
      then colour (bitsToNat (decodeSecond pr.1)) (decodeFirst pr.2) (decodeSecond pr.2)
    else bif decide (bitsToNat (decodeFirst pr.1) = 1)
      then idcPre c (pairCode (decodeSecond pr.1) (decodeFirst pr.2)) (decodeSecond pr.2)
      else idcPre c' (pairCode (decodeSecond pr.1) (decodeFirst pr.2)) (decodeSecond pr.2)
/-- Helper. -/
theorem idcDecomp_partrec (colour : ℕ → BitString → BitString →. BitString)
    (h : Partrec (fun q : (ℕ × BitString) × BitString => colour q.1.1 q.1.2 q.2)) (c c' : Code) :
    Partrec (idcDecomp colour c c') := by
  have hc0 : Computable (fun pr : BitString × BitString =>
      decide (bitsToNat (decodeFirst pr.1) = 0)) :=
    ((PrimrecRel.decide Primrec.eq).comp
      (bitsToNat_primrec.comp (CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.fst))
      (Primrec.const 0)).to_comp
  have hc1 : Computable (fun pr : BitString × BitString =>
      decide (bitsToNat (decodeFirst pr.1) = 1)) :=
    ((PrimrecRel.decide Primrec.eq).comp
      (bitsToNat_primrec.comp (CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.fst))
      (Primrec.const 1)).to_comp
  have hE0 := h.comp (Computable.pair (Computable.pair
      (bitsToNat_primrec.to_comp.comp (decodeSecond_computable.comp Computable.fst))
      (decodeFirst_computable.comp Computable.snd)) (decodeSecond_computable.comp Computable.snd))
  have hg := Computable.pair ((show Computable₂ (fun x y : BitString => pairCode x y) from
      pairCode_computable).comp (decodeSecond_computable.comp Computable.fst)
      (decodeFirst_computable.comp Computable.snd)) (decodeSecond_computable.comp Computable.snd)
  have hE1 := (idcPre_partrec c).comp hg
  have hE2 := (idcPre_partrec c').comp hg
  exact (Partrec.cond hc0 hE0 (Partrec.cond hc1 hE1 hE2)).of_eq fun _ => rfl
/-- Helper. -/
theorem idcDecomp_zero (colour : ℕ → BitString → BitString →. BitString)
    (c c' : Code) (k : ℕ) (A B : BitString) :
    idcDecomp colour c c' (pairCode (Nat.bits 0) (Nat.bits k), pairCode A B) = colour k A B := by
  simp only [idcDecomp, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
  rfl
/-- Helper. -/
theorem idcDecomp_one (colour : ℕ → BitString → BitString →. BitString)
    (c c' : Code) (k : ℕ) (A X : BitString) :
    idcDecomp colour c c' (pairCode (Nat.bits 1) (Nat.bits k), pairCode A X)
      = idcPre c (pairCode (Nat.bits k) A) X := by
  simp only [idcDecomp, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
  rfl
/-- Helper. -/
theorem idcDecomp_two (colour : ℕ → BitString → BitString →. BitString)
    (c c' : Code) (k : ℕ) (B X : BitString) :
    idcDecomp colour c c' (pairCode (Nat.bits 2) (Nat.bits k), pairCode B X)
      = idcPre c' (pairCode (Nat.bits k) B) X := by
  simp only [idcDecomp, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
  rfl
end IdcDecompressor
/-- Helper. -/
theorem informationDistance_decompressor_of_colouring
    (D : Map) (colour : ℕ → BitString → BitString →. BitString)
    (hcolour : IsInformationDistanceColouring D colour) :
    ∃ E : Map, Partrec E ∧ ∃ a : ℕ, ∀ (k : ℕ) (A B : BitString),
      condK D A B < (k : ℕ∞) → condK D B A < (k : ℕ∞) →
      ∃ X : BitString, X.length = k + 1 ∧
        condK E A (pairCode B X) ≤ (logSlack a k : ℕ∞) ∧
        condK E B (pairCode A X) ≤ (logSlack a k : ℕ∞) ∧
        condK E X (pairCode A B) ≤ (logSlack a k : ℕ∞) := by
  obtain ⟨hcP, hcProp⟩ := hcolour
  obtain ⟨c, hc⟩ : ∃ c : Nat.Partrec.Code, IsCodeFor c (idcColourMap colour) :=
    Nat.Partrec.Code.exists_code.mp (idcColourMap_partrec colour hcP)
  obtain ⟨c', hc'⟩ : ∃ c' : Nat.Partrec.Code, IsCodeFor c' (idcColourMapSwap colour) :=
    Nat.Partrec.Code.exists_code.mp (idcColourMapSwap_partrec colour hcP)
  refine ⟨idcDecomp colour c c', idcDecomp_partrec colour hcP c c', 5, fun k A B hAB hBA => ?_⟩
  obtain ⟨X, hXmem, hXlen, hdetB, hdetA⟩ := hcProp k A B hAB hBA
  refine ⟨X, hXlen, ?_, ?_, ?_⟩
  · refine (condK_le_iff _ A (pairCode B X) (logSlack 5 k)).2
      ⟨pairCode (Nat.bits 2) (Nat.bits k), ?_, ?_⟩
    · have h2 : (Nat.bits 2).length ≤ 2 := length_natBits_le 2
      simp only [programLength, length_pairCode, logSlack]
      omega
    · have hmem : A ∈ idcDecomp colour c c' (pairCode (Nat.bits 2) (Nat.bits k), pairCode B X) := by
        rw [idcDecomp_two]
        refine idcPre_mem_unique hc' ?_ ?_
        · simp only [idcColourMapSwap, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
          exact hXmem
        · intro w hw
          simp only [idcColourMapSwap, decodeFirst_pairCode, decodeSecond_pairCode,
            bitsToNat_bits] at hw
          exact hdetA w hw
      exact hmem
  · refine (condK_le_iff _ B (pairCode A X) (logSlack 5 k)).2
      ⟨pairCode (Nat.bits 1) (Nat.bits k), ?_, ?_⟩
    · have h1 : (Nat.bits 1).length ≤ 1 := length_natBits_le 1
      simp only [programLength, length_pairCode, logSlack]
      omega
    · have hmem : B ∈ idcDecomp colour c c' (pairCode (Nat.bits 1) (Nat.bits k), pairCode A X) := by
        rw [idcDecomp_one]
        refine idcPre_mem_unique hc ?_ ?_
        · simp only [idcColourMap, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
          exact hXmem
        · intro w hw
          simp only [idcColourMap, decodeFirst_pairCode, decodeSecond_pairCode,
            bitsToNat_bits] at hw
          exact hdetB w hw
      exact hmem
  · refine (condK_le_iff _ X (pairCode A B) (logSlack 5 k)).2
      ⟨pairCode (Nat.bits 0) (Nat.bits k), ?_, ?_⟩
    · have h0 : (Nat.bits 0).length = 0 := by simp
      simp only [programLength, length_pairCode, logSlack]
      omega
    · have hmem : X ∈ idcDecomp colour c c' (pairCode (Nat.bits 0) (Nat.bits k), pairCode A B) := by
        rw [idcDecomp_zero]
        exact hXmem
      exact hmem
/-- Helper. -/
theorem transfer_informationDistance_bounds
    (D E : Map) (hD : isOptimalConditional D) (hE : Partrec E) (a : ℕ) :
    ∃ c : ℕ, ∀ (k : ℕ) (A B X : BitString),
      condK E A (pairCode B X) ≤ (logSlack a k : ℕ∞) →
      condK E B (pairCode A X) ≤ (logSlack a k : ℕ∞) →
      condK E X (pairCode A B) ≤ (logSlack a k : ℕ∞) →
      condK D A (pairCode B X) ≤ (logSlack c k : ℕ∞) ∧
        condK D B (pairCode A X) ≤ (logSlack c k : ℕ∞) ∧
        condK D X (pairCode A B) ≤ (logSlack c k : ℕ∞) := by
  obtain ⟨b, hb⟩ := hD.2 E hE
  refine ⟨a + b, fun k A B X hA hB hX => ?_⟩
  have hSlackNat : logSlack a k + b ≤ logSlack (a + b) k := by
    rw [logSlack_add_constants]
    apply Nat.add_le_add_left
    unfold logSlack
    omega
  have hSlack : (logSlack a k : ℕ∞) + (b : ℕ∞) ≤
      (logSlack (a + b) k : ℕ∞) := by
    exact_mod_cast hSlackNat
  exact ⟨(hb A (pairCode B X)).trans ((add_le_add_left hA _).trans hSlack),
    (hb B (pairCode A X)).trans ((add_le_add_left hB _).trans hSlack),
    (hb X (pairCode A B)).trans ((add_le_add_left hX _).trans hSlack)⟩
/-- Under both `< k` bounds, one `(k+1)`-bit string works in both directions and given the pair.
The book suppresses the `+1`. SUV Theorem 232, p. 377. -/
theorem exists_informationDistanceCode (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (k : ℕ) (A B : BitString),
      condK D A B < (k : ℕ∞) → condK D B A < (k : ℕ∞) →
      ∃ X : BitString, X.length = k + 1 ∧
        condK D A (pairCode B X) ≤ (logSlack c k : ℕ∞) ∧
        condK D B (pairCode A X) ≤ (logSlack c k : ℕ∞) ∧
        condK D X (pairCode A B) ≤ (logSlack c k : ℕ∞) := by
  obtain ⟨colour, hcolour⟩ := exists_informationDistance_colouring D hD.1
  obtain ⟨E, hE, a, ha⟩ :=
    informationDistance_decompressor_of_colouring D colour hcolour
  obtain ⟨c, hc⟩ := transfer_informationDistance_bounds D E hD hE a
  refine ⟨c, fun k A B hAB hBA => ?_⟩
  obtain ⟨X, hlen, hA, hB, hX⟩ := ha k A B hAB hBA
  exact ⟨X, hlen, hc k A B X hA hB hX⟩
/-- Helper. -/
theorem xorStr_plainK_pairCode_swap_le (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ x y : BitString,
      plainK D (pairCode y x) ≤ plainK D (pairCode x y) + (c : ℕ∞) := by
  let swap : BitString → BitString := fun w =>
    pairCode (decodeSecond w) (decodeFirst w)
  have hEq : swap = (fun p : BitString × BitString => pairCode p.1 p.2) ∘
      (fun w : BitString => (decodeSecond w, decodeFirst w)) := by
    funext w
    rfl
  have hSwap : Computable swap := by
    rw [hEq]
    exact pairCode_computable.comp
      (decodeSecond_computable.pair decodeFirst_computable)
  obtain ⟨c, hc⟩ := plainK_map_le D hD swap hSwap
  refine ⟨c, fun x y => ?_⟩
  simpa [swap, decodeFirst_pairCode, decodeSecond_pairCode] using hc (pairCode x y)
/-- Helper. -/
theorem xorStr_condK_lower_bounds
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (n : ℕ) (A B : BitString), A.length = n → B.length = n →
      ((2 * n : ℕ) : ℕ∞) ≤ plainK D (pairCode A B) + (logSlack c₀ n : ℕ∞) →
      (n : ℕ∞) ≤ condK D A B + (logSlack c n : ℕ∞) ∧
        (n : ℕ∞) ≤ condK D B A + (logSlack c n : ℕ∞) := by
  obtain ⟨cU, hU⟩ := pairPlainK_chain_upper_values D hD
  obtain ⟨cS, hS⟩ := xorStr_plainK_pairCode_swap_le D hD
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  obtain ⟨cAbs, hAbs⟩ := logSlack_absorb_of_le_linear cU 3 (2 + cLen)
  refine ⟨c₀ + cLen + cAbs + cS, fun n A B hAlen hBlen hPair => ?_⟩
  obtain ⟨kA, hkA⟩ := exists_plainComplexityValue D hD A
  obtain ⟨kB, hkB⟩ := exists_plainComplexityValue D hD B
  obtain ⟨kAB, hkAB⟩ := exists_plainComplexityValue D hD (pairCode A B)
  obtain ⟨kBA, hkBA⟩ := exists_plainComplexityValue D hD (pairCode B A)
  obtain ⟨kAgB, hkAgB⟩ := exists_plainConditionalComplexityValue D hD A B
  obtain ⟨kBgA, hkBgA⟩ := exists_plainConditionalComplexityValue D hD B A
  have hUpAB := hU A B kA kBgA kAB hkA hkBgA hkAB
  have hUpBA := hU B A kB kAgB kBA hkB hkAgB hkBA
  have hkA' : plainK D A = (kA : ℕ∞) := hkA
  have hkB' : plainK D B = (kB : ℕ∞) := hkB
  have hkAB' : plainK D (pairCode A B) = (kAB : ℕ∞) := hkAB
  have hkBA' : plainK D (pairCode B A) = (kBA : ℕ∞) := hkBA
  have hkAgB' : condK D A B = (kAgB : ℕ∞) := hkAgB
  have hkBgA' : condK D B A = (kBgA : ℕ∞) := hkBgA
  have hSw : kAB ≤ kBA + cS := by
    have h := hS B A
    rw [hkAB', hkBA'] at h
    exact_mod_cast h
  have hAComplexity : kA ≤ n + cLen := by
    have h := hLen A
    rw [hkA', programLength, hAlen] at h
    exact_mod_cast h
  have hBComplexity : kB ≤ n + cLen := by
    have h := hLen B
    rw [hkB', programLength, hBlen] at h
    exact_mod_cast h
  have hABLength : kAB + 1 ≤ 3 * n + (2 + cLen) := by
    have h := hLen (pairCode A B)
    rw [hkAB', programLength, length_pairCode, hAlen, hBlen] at h
    have h' : kAB ≤ n + 1 + n + n + cLen := by exact_mod_cast h
    omega
  have hBALength : kBA + 1 ≤ 3 * n + (2 + cLen) := by
    have h := hLen (pairCode B A)
    rw [hkBA', programLength, length_pairCode, hBlen, hAlen] at h
    have h' : kBA ≤ n + 1 + n + n + cLen := by exact_mod_cast h
    omega
  have hAbsAB : logSlack cU (kAB + 1) ≤ logSlack cAbs n :=
    hAbs n (kAB + 1) hABLength
  have hAbsBA : logSlack cU (kBA + 1) ≤ logSlack cAbs n :=
    hAbs n (kBA + 1) hBALength
  have hPairNat : 2 * n ≤ kAB + logSlack c₀ n := by
    rw [hkAB'] at hPair
    exact_mod_cast hPair
  have hLenSlack : cLen ≤ logSlack cLen n := by
    unfold logSlack
    omega
  have hSwapSlack : cS ≤ logSlack cS n := by
    unfold logSlack
    omega
  have hAgB : n ≤ kAgB + logSlack (c₀ + cLen + cAbs + cS) n := by
    rw [logSlack_add_constants, logSlack_add_constants, logSlack_add_constants]
    omega
  have hBgA : n ≤ kBgA + logSlack (c₀ + cLen + cAbs + cS) n := by
    rw [logSlack_add_constants, logSlack_add_constants, logSlack_add_constants]
    omega
  constructor
  · rw [hkAgB']; exact_mod_cast hAgB
  · rw [hkBgA']; exact_mod_cast hBgA
/-- Helper. -/
theorem xorStr_const_complexity_bounds (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ A B : BitString, A.length = B.length →
      condK D A (pairCode B (xorStr A B)) ≤ (c : ℕ∞) ∧
      condK D B (pairCode A (xorStr A B)) ≤ (c : ℕ∞) ∧
      condK D (xorStr A B) (pairCode A B) ≤ (c : ℕ∞) := by
  have hDecodeRight : Computable (fun s : BitString =>
      xorStr (decodeSecond s) (decodeFirst s)) :=
    xorStr_primrec.to_comp.comp decodeSecond_computable decodeFirst_computable
  have hDecodeLeft : Computable (fun s : BitString =>
      xorStr (decodeFirst s) (decodeSecond s)) :=
    xorStr_primrec.to_comp.comp decodeFirst_computable decodeSecond_computable
  obtain ⟨cRight, hcRight⟩ := condK_comp D hD _ hDecodeRight
  obtain ⟨cLeft, hcLeft⟩ := condK_comp D hD _ hDecodeLeft
  obtain ⟨cXor, hcXor⟩ := condK_comp D hD _ hDecodeLeft
  refine ⟨cRight + cLeft + cXor, fun A B hlen => ?_⟩
  have hA := hcRight (pairCode B (xorStr A B))
  have hB := hcLeft (pairCode A (xorStr A B))
  have hX := hcXor (pairCode A B)
  rw [decodeFirst_pairCode, decodeSecond_pairCode, xorStr_xorStr_right] at hA
  rw [decodeFirst_pairCode, decodeSecond_pairCode, xorStr_xorStr_left A B hlen] at hB
  rw [decodeFirst_pairCode, decodeSecond_pairCode] at hX
  refine ⟨hA.trans ?_, hB.trans ?_, hX.trans ?_⟩
  · exact_mod_cast (show cRight ≤ cRight + cLeft + cXor by omega)
  · exact_mod_cast (show cLeft ≤ cRight + cLeft + cXor by omega)
  · exact_mod_cast (show cXor ≤ cRight + cLeft + cXor by omega)
/-- For independent random `n`-bit strings, `xor` satisfies Theorem 232 up to `O(log n)`;
its upper bounds hold for all strings. SUV Problem 322, p. 378. -/
theorem xorStr_informationDistanceCode (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (n : ℕ) (A B : BitString), A.length = n → B.length = n →
      (n : ℕ∞) ≤ plainK D A + (logSlack c₀ n : ℕ∞) →
      (n : ℕ∞) ≤ plainK D B + (logSlack c₀ n : ℕ∞) →
      ((2 * n : ℕ) : ℕ∞) ≤ plainK D (pairCode A B) + (logSlack c₀ n : ℕ∞) →
      (xorStr A B).length = n ∧
      (n : ℕ∞) ≤ condK D A B + (logSlack c n : ℕ∞) ∧
      (n : ℕ∞) ≤ condK D B A + (logSlack c n : ℕ∞) ∧
      condK D A (pairCode B (xorStr A B)) ≤ (logSlack c n : ℕ∞) ∧
      condK D B (pairCode A (xorStr A B)) ≤ (logSlack c n : ℕ∞) ∧
      condK D (xorStr A B) (pairCode A B) ≤ (logSlack c n : ℕ∞) := by
  obtain ⟨cLower, hLower⟩ := xorStr_condK_lower_bounds D hD c₀
  obtain ⟨cXor, hXor⟩ := xorStr_const_complexity_bounds D hD
  refine ⟨cLower + cXor, fun n A B hAlen hBlen _ _ hPair => ?_⟩
  have hlen : A.length = B.length := hAlen.trans hBlen.symm
  obtain ⟨hAB, hBA⟩ := hLower n A B hAlen hBlen hPair
  obtain ⟨hA, hB, hX⟩ := hXor A B hlen
  have hLowerSlack : (logSlack cLower n : ℕ∞) ≤
      (logSlack (cLower + cXor) n : ℕ∞) := by
    exact_mod_cast logSlack_mono_left (Nat.le_add_right cLower cXor) n
  have hXorSlack : (cXor : ℕ∞) ≤ (logSlack (cLower + cXor) n : ℕ∞) := by
    exact_mod_cast (show cXor ≤ logSlack (cLower + cXor) n by
      unfold logSlack
      omega)
  refine ⟨by simp [hAlen], hAB.trans ?_, hBA.trans ?_, hA.trans hXorSlack,
    hB.trans hXorSlack, hX.trans hXorSlack⟩
  · exact add_le_add_right hLowerSlack _
  · exact add_le_add_right hLowerSlack _
/-- For equal-length strings the `xor` bounds hold with `O(1)`; independence fixes the capacity.
SUV Problem 322, p. 378 (unconditional part). -/
theorem xorStr_informationDistanceCode_const (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ A B : BitString, A.length = B.length →
      (xorStr A B).length = A.length ∧
      condK D A (pairCode B (xorStr A B)) ≤ (c : ℕ∞) ∧
      condK D B (pairCode A (xorStr A B)) ≤ (c : ℕ∞) ∧
      condK D (xorStr A B) (pairCode A B) ≤ (c : ℕ∞) := by
  obtain ⟨c, hc⟩ := xorStr_const_complexity_bounds D hD
  exact ⟨c, fun A B hlen => ⟨length_xorStr A B, hc A B hlen⟩⟩
/-- With unequal bounds, a `(k+1)`-bit string works both ways and its `(l+1)` prefix works one way.
The added bits record the suppressed `O(1)`. SUV Theorem 233, p. 379. -/
theorem exists_informationDistanceCode_prefix (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (k l : ℕ) (A B : BitString), l < k →
      condK D A B < (k : ℕ∞) → condK D B A < (l : ℕ∞) →
      ∃ X : BitString, X.length = k + 1 ∧
        condK D X (pairCode A B) ≤ (logSlack c k : ℕ∞) ∧
        condK D A (pairCode B X) ≤ (logSlack c k : ℕ∞) ∧
        condK D B (pairCode A (X.take (l + 1))) ≤ (logSlack c k : ℕ∞) := by
  obtain ⟨c, hc⟩ : ∃ c : Nat.Partrec.Code, IsCodeFor c D :=
    Nat.Partrec.Code.exists_code.mp hD.1
  obtain ⟨b0, hb0⟩ := hD.2 (idcMap c 0) (idcMap_partrec c 0)
  obtain ⟨b1, hb1⟩ := hD.2 (idcMap c 1) (idcMap_partrec c 1)
  obtain ⟨b2, hb2⟩ := hD.2 (idcMap c 2) (idcMap_partrec c 2)
  refine ⟨3 + b0 + b1 + b2, fun k l A B hlk hAB hBA => ?_⟩
  obtain ⟨s, X, hX⟩ := idcAssign_covers (kl := (k, l)) (e := (A, B)) hc hlk.le ⟨hAB, hBA⟩
  refine ⟨X, idcAssign_length hX, ?_, ?_, ?_⟩
  · exact idcMap_bound D c 0 b0 _ hb0 (by omega) hlk.le
      (idcFind_spec (mode := 0) (uv := (A, B)) hX (by simp [idcMatch]))
  · exact idcMap_bound D c 1 b1 _ hb1 (by omega) hlk.le
      (idcFind_spec (mode := 1) (uv := (B, X)) hX (by simp [idcMatch]))
  · exact idcMap_bound D c 2 b2 _ hb2 (by omega) hlk.le
      (idcFind_spec (mode := 2) (uv := (A, X.take (l + 1))) hX (by simp [idcMatch]))
/-- Helper. -/
def idcSplitMap (D : Map) : Map := fun pr =>
  (D (decodeFirst (decodeSecond pr.1), pr.2)).bind fun B =>
    (D (decodeSecond (decodeSecond pr.1), pairCode (decodeFirst pr.2) B)).map fun Z =>
      pairCode B (Z.drop (bitsToNat (decodeFirst pr.1)))
/-- Helper. -/
theorem idcSplitMap_partrec (D : Map) (hD : Partrec D) :
    Partrec (idcSplitMap D) := by
  have hFirst : Partrec (fun pr : BitString × BitString =>
      D (decodeFirst (decodeSecond pr.1), pr.2)) :=
    hD.comp ((decodeFirst_computable.comp (decodeSecond_computable.comp Computable.fst)).pair
      Computable.snd)
  have hSecond : Partrec (fun q : (BitString × BitString) × BitString =>
      D (decodeSecond (decodeSecond q.1.1), pairCode (decodeFirst q.1.2) q.2)) := by
    refine hD.comp ((decodeSecond_computable.comp
      (decodeSecond_computable.comp (Computable.fst.comp Computable.fst))).pair ?_)
    exact (show Computable₂ (fun x y : BitString => pairCode x y) from
      pairCode_computable).comp
        (decodeFirst_computable.comp (Computable.snd.comp Computable.fst)) Computable.snd
  have hOut : Computable (fun q : ((BitString × BitString) × BitString) × BitString =>
      pairCode q.1.2 (q.2.drop (bitsToNat (decodeFirst q.1.1.1)))) := by
    refine (show Computable₂ (fun x y : BitString => pairCode x y) from
      pairCode_computable).comp (Computable.snd.comp Computable.fst) ?_
    exact (Primrec.list_drop.comp
      (bitsToNat_primrec.comp (CodedFiniteDistribution.decodeFirst_primrec.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))) Primrec.snd).to_comp
  exact Partrec.bind hFirst (Partrec.map hSecond hOut)
/-- Helper. -/
theorem condK_idcSplit_le (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (n : ℕ) (A B Z : BitString) (e : ℕ),
      condK D B (pairCode A (Z.take n)) ≤ (e : ℕ∞) →
      condK D Z (pairCode A B) ≤ (e : ℕ∞) →
      condK D (pairCode B (Z.drop n)) (pairCode A (Z.take n)) ≤
        ((3 * e + 2 * (Nat.bits n).length + c : ℕ) : ℕ∞) := by
  obtain ⟨c, hc⟩ := hD.2 (idcSplitMap D) (idcSplitMap_partrec D hD.1)
  refine ⟨c + 2, fun n A B Z e hB hZ => ?_⟩
  obtain ⟨q, hqLen, hq⟩ := (condK_le_iff D B (pairCode A (Z.take n)) e).1 hB
  obtain ⟨p, hpLen, hp⟩ := (condK_le_iff D Z (pairCode A B) e).1 hZ
  change q.length ≤ e at hqLen
  change p.length ≤ e at hpLen
  let r := pairCode (Nat.bits n) (pairCode q p)
  have hr : pairCode B (Z.drop n) ∈
      idcSplitMap D (r, pairCode A (Z.take n)) := by
    simp only [idcSplitMap, r, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
    exact Part.mem_bind hq (Part.mem_map _ hp)
  have hE : condK (idcSplitMap D) (pairCode B (Z.drop n))
      (pairCode A (Z.take n)) ≤ (r.length : ℕ∞) :=
    (condK_le_iff _ _ _ _).2 ⟨r, le_rfl, hr⟩
  calc
    condK D (pairCode B (Z.drop n)) (pairCode A (Z.take n))
        ≤ condK (idcSplitMap D) (pairCode B (Z.drop n))
          (pairCode A (Z.take n)) + (c : ℕ∞) := hc _ _
    _ ≤ (r.length : ℕ∞) + (c : ℕ∞) := by gcongr
    _ ≤ ((3 * e + 2 * (Nat.bits n).length + (c + 2) : ℕ) : ℕ∞) := by
      exact_mod_cast (show r.length + c ≤
        3 * e + 2 * (Nat.bits n).length + (c + 2) by
          simp only [r, length_pairCode]
          omega)
/-- Helper. -/
def idcJoinCondition (w : BitString) : BitString :=
  pairCode (decodeFirst w)
    (decodeFirst (decodeSecond (decodeSecond w)) ++ decodeFirst (decodeSecond w))
/-- Helper. -/
theorem idcJoinCondition_computable : Computable idcJoinCondition := by
  unfold idcJoinCondition
  refine (show Computable₂ (fun x y : BitString => pairCode x y) from
    pairCode_computable).comp decodeFirst_computable ?_
  exact Computable.list_append.comp
    (decodeFirst_computable.comp (decodeSecond_computable.comp decodeSecond_computable))
    (decodeFirst_computable.comp decodeSecond_computable)
/-- Helper. -/
@[simp] theorem idcJoinCondition_listCode (B Y X : BitString) :
    idcJoinCondition (listCode [B, Y, X]) = pairCode B (X ++ Y) := by
  simp only [idcJoinCondition, listCode_cons, decodeFirst_pairCode, decodeSecond_pairCode]
/-- Theorem 233 as used in [9]: split the message, retaining the off-by-one, with both resulting
conditional complexities logarithmic. SUV Problem 323, p. 379. -/
theorem exists_informationDistanceCode_split (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (k l : ℕ) (A B : BitString), l < k →
      condK D A B < (k : ℕ∞) → condK D B A < (l : ℕ∞) →
      ∃ X Y : BitString, X.length = l + 1 ∧ Y.length = k - l ∧
        condK D (pairCode B Y) (pairCode A X) ≤ (logSlack c k : ℕ∞) ∧
        condK D A (listCode [B, Y, X]) ≤ (logSlack c k : ℕ∞) := by
  obtain ⟨c₀, hc₀⟩ := exists_informationDistanceCode_prefix D hD
  obtain ⟨cSplit, hSplit⟩ := condK_idcSplit_le D hD
  obtain ⟨cJoin, hJoin⟩ := condK_cond_map_le D hD idcJoinCondition
    idcJoinCondition_computable
  refine ⟨3 * c₀ + 2 + cSplit + cJoin, fun k l A B hlk hAB hBA => ?_⟩
  obtain ⟨Z, hZlen, hZ, hA, hB⟩ := hc₀ k l A B hlk hAB hBA
  let X := Z.take (l + 1)
  let Y := Z.drop (l + 1)
  refine ⟨X, Y, ?_, ?_, ?_, ?_⟩
  · simp only [X, List.length_take, hZlen]; omega
  · simp only [Y, List.length_drop, hZlen]; omega
  · refine (hSplit (l + 1) A B Z (logSlack c₀ k) hB hZ).trans ?_
    have hbits : (Nat.bits (l + 1)).length ≤ (Nat.bits k).length :=
      length_natBits_mono (by omega)
    exact_mod_cast (show 3 * logSlack c₀ k + 2 * (Nat.bits (l + 1)).length + cSplit ≤
      logSlack (3 * c₀ + 2 + cSplit + cJoin) k by
        unfold logSlack
        nlinarith)
  · have hcond := hJoin A (listCode [B, Y, X])
    rw [idcJoinCondition_listCode] at hcond
    have hXY : X ++ Y = Z := List.take_append_drop (l + 1) Z
    rw [hXY] at hcond
    calc
      condK D A (listCode [B, Y, X])
          ≤ condK D A (pairCode B Z) + (cJoin : ℕ∞) := hcond
      _ ≤ (logSlack c₀ k : ℕ∞) + (cJoin : ℕ∞) := by gcongr
      _ ≤ (logSlack (3 * c₀ + 2 + cSplit + cJoin) k : ℕ∞) := by
        exact_mod_cast (show logSlack c₀ k + cJoin ≤
          logSlack (3 * c₀ + 2 + cSplit + cJoin) k by
            unfold logSlack
            nlinarith)
end Kolmogorov
