import KolmogorovMathlib.CommonInformation.PlainSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith

/-!
# C7: Conditional independence and common information (SUV Theorem 228)

This file formalizes **SUV Theorem 228** (p. 362): for arbitrary strings
`x, y, z, u, v`,
```
C(z) ≤ 2·C(z|x) + 2·C(z|y) + I(x:y|u) + I(x:y|v) + I(u:v)
```
with `O(log C(x,y,u,z,v))` precision.

Following the chapter conventions we keep **plain** complexity throughout and
express every mutual-information term by its exact additive, subtraction-free
form:
```
I(x:y|u) = C(x|u) + C(y|u) − C(x,y|u),   I(u:v) = C(u) + C(v) − C(u,v).
```
Multiplying out and moving all subtracted terms to the left, Theorem 228 becomes
the fully subtraction-free inequality
```
C(z) + C(x,y|u) + C(x,y|v) + C(u,v)
    ≤ 2·C(z|x) + 2·C(z|y) + C(x|u) + C(y|u) + C(x|v) + C(y|v) + C(u) + C(v) + O(log).
```
This is `theorem_228_conditional_independence_bound`, stated in the chapter's
*values* form (`HasPlainComplexityValue` / `HasPlainConditionalComplexityValue`
witnesses, one uniform `logSlack C`).

## Proof architecture

SUV's proof is a purely arithmetical combination of one inequality applied to
three contexts.  The single ingredient is the complexity form of the Shannon
inequality of Problem 296 (p. 341), relativized to a context `w`:
```
C(z|w) ≤ C(z|a,w) + C(z|b,w) + I(a:b|w)          (subtraction-free:)
C(z|w) + C(a,b|w) ≤ C(z|a,w) + C(z|b,w) + C(a|w) + C(b|w) + O(log).
```
This is `base_conditional_mutualInformation_inequality`.  Its proof first
derives plain conditional symmetry of information, uniformly in `w`, from the
repository's conditional prefix-symmetry theorem.  It then proves the needed
submodularity inequality through conditional pair coding, computable pair
swaps, and projection of a coded triple.

`theorem_228_conditional_independence_bound` is then derived with a complete,
kernel-checked reduction:
* the base inequality at `(z, u, v, [])`, `(z, x, y, u)`, `(z, x, y, v)`;
* `condK_condPair_left_le` (condition monotonicity `C(z|a,w) ≤ C(z|a) + O(1)`,
  proved below), which turns the six relativized conditional complexities into
  the four appearing in the statement.

**Exercises 314–316** (the fixed-frequency stochastic construction) are *not*
formalized here: they additionally require the absent SUV Section 7
(Theorem 146) entropy↔complexity bridge, whose formalization is a separate,
human-gated decision (see `PLAN_COMMON_INFORMATION.md`, milestone C7).  They are
deliberately omitted rather than represented by fake statements.
-/

namespace Kolmogorov

/-- `C(x | []) = C(x)`: a plain-complexity witness is a conditional witness with
empty context (definitional, since `plainK V x = condK V x []`). -/
theorem hasCondValue_nil_of_hasPlainValue {V : Map} {x : BitString} {k : Nat}
    (h : HasPlainComplexityValue V x k) :
    HasPlainConditionalComplexityValue V x [] k := h

/-- **Condition monotonicity.** Enlarging the condition of a plain conditional
complexity by pairing on extra data can only decrease it, up to a constant:
`C(z | pairCode a w) ≤ C(z | a) + O(1)`.  Indeed from `pairCode a w` the machine
can recover `a` (`decodeFirst`), so any program producing `z` from `a` produces
`z` from `pairCode a w` at the same length. -/
theorem condK_condPair_left_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ z a w : BitString,
      condK V z (pairCode a w) ≤ condK V z a + (c : ENat) := by
  classical
  -- `D` runs `V` after stripping the extra `w` from the condition.
  set D : Map := fun q => V (q.1, decodeFirst q.2) with hDdef
  have hDdec : isDecompressor D :=
    hV.1.comp (Computable.fst.pair (decodeFirst_computable.comp Computable.snd))
  obtain ⟨c, hc⟩ := hV.2 D hDdec
  refine ⟨c, fun z a w => ?_⟩
  -- The candidate program-length sets for `D` (condition `pairCode a w`) and for
  -- `V` (condition `a`) coincide.
  have hset : candidateLengths D z (pairCode a w) = candidateLengths V z a := by
    ext n
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, by simpa [hDdef, produces, decodeFirst_pairCode] using hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, by simpa [hDdef, produces, decodeFirst_pairCode] using hp, rfl⟩
  have hcond : condK D z (pairCode a w) = condK V z a := by
    unfold condK; rw [hset]
  calc condK V z (pairCode a w)
      ≤ condK D z (pairCode a w) + (c : ENat) := hc z (pairCode a w)
    _ = condK V z a + (c : ENat) := by rw [hcond]

/-- Adding a left component to a condition can only decrease plain conditional
complexity, up to a uniform constant. -/
theorem condK_condPair_right_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ z a w : BitString,
      condK V z (pairCode a w) ≤ condK V z w + (c : ENat) := by
  classical
  set D : Map := fun q => V (q.1, decodeSecond q.2) with hDdef
  have hDdec : isDecompressor D :=
    hV.1.comp (Computable.fst.pair (decodeSecond_computable.comp Computable.snd))
  obtain ⟨c, hc⟩ := hV.2 D hDdec
  refine ⟨c, fun z a w => ?_⟩
  have hset : candidateLengths D z (pairCode a w) = candidateLengths V z w := by
    ext n
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, by simpa [hDdef, produces, decodeSecond_pairCode] using hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, by simpa [hDdef, produces, decodeSecond_pairCode] using hp, rfl⟩
  have hcond : condK D z (pairCode a w) = condK V z w := by
    unfold condK
    rw [hset]
  calc
    condK V z (pairCode a w)
        ≤ condK D z (pairCode a w) + (c : ENat) := hc z (pairCode a w)
    _ = condK V z w + (c : ENat) := by rw [hcond]

/-- Projecting the second component of a conditionally described pair costs
only a uniform constant. -/
theorem condK_drop_left
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x y w : BitString, ∀ kxy ky : ℕ,
      HasPlainConditionalComplexityValue V (pairCode x y) w kxy →
      HasPlainConditionalComplexityValue V y w ky →
      ky ≤ kxy + c := by
  let D : Map := fun pr => (V (pr.1, pr.2)).map decodeSecond
  have hD : isDecompressor D :=
    Partrec.map hV.1 (decodeSecond_computable.comp Computable.snd)
  obtain ⟨cD, hcD⟩ := hV.2 D hD
  refine ⟨cD, fun x y w kxy ky hxy hy => ?_⟩
  obtain ⟨pxy, hpxy, hpLen⟩ := hxy.exists_program
  have hDProd : produces D pxy w y := by
    change y ∈ (V (pxy, w)).map decodeSecond
    rw [← decodeSecond_pairCode x y]
    exact Part.mem_map _ hpxy
  have hbound : condK V y w ≤ (pxy.length : ENat) + (cD : ENat) :=
    (hcD y w).trans (by
      gcongr
      exact sInf_le ⟨pxy, hDProd, rfl⟩)
  have hbound' : (ky : ENat) ≤ ((kxy + cD : Nat) : ENat) := by
    calc
      (ky : ENat) = condK V y w := hy.symm
      _ ≤ (pxy.length : ENat) + (cD : ENat) := hbound
      _ = ((kxy + cD : Nat) : ENat) := by rw [hpLen, Nat.cast_add]
  exact_mod_cast hbound'

/-- Reassociate the condition used by conditional prefix symmetry:
`(w,(x,k)) ↦ ((x,w),k)`. -/
def condContextReassociate (q : BitString) : BitString :=
  pairCode
    (pairCode (decodeFirst (decodeSecond q)) (decodeFirst q))
    (decodeSecond (decodeSecond q))

theorem condContextReassociate_computable : Computable condContextReassociate := by
  have hLeft : Computable (fun q : BitString =>
      pairCode (decodeFirst (decodeSecond q)) (decodeFirst q)) :=
    (show Computable₂ (fun a b : BitString => pairCode a b) from pairCode_computable).comp
      (decodeFirst_computable.comp decodeSecond_computable) decodeFirst_computable
  exact (show Computable₂ (fun a b : BitString => pairCode a b) from pairCode_computable).comp
    hLeft (decodeSecond_computable.comp decodeSecond_computable)

@[simp] theorem condContextReassociate_prefixCondComplexityContext
    (w x : BitString) (k : Nat) :
    condContextReassociate (prefixCondComplexityContext w x k) =
      pairCode (pairCode x w) (natCode k) := by
  unfold condContextReassociate prefixCondComplexityContext
  simp only [decodeFirst_pairCode, decodeSecond_pairCode]

/-- Inverse reassociation on well-formed conditional-prefix contexts:
`((x,w),k) ↦ (w,(x,k))`. -/
def condContextAssociate (q : BitString) : BitString :=
  pairCode
    (decodeSecond (decodeFirst q))
    (pairCode (decodeFirst (decodeFirst q)) (decodeSecond q))

theorem condContextAssociate_computable : Computable condContextAssociate := by
  have hRight : Computable (fun q : BitString =>
      pairCode (decodeFirst (decodeFirst q)) (decodeSecond q)) :=
    (show Computable₂ (fun a b : BitString => pairCode a b) from pairCode_computable).comp
      (decodeFirst_computable.comp decodeFirst_computable) decodeSecond_computable
  exact (show Computable₂ (fun a b : BitString => pairCode a b) from pairCode_computable).comp
    (decodeSecond_computable.comp decodeFirst_computable) hRight

@[simp] theorem condContextAssociate_pairCode
    (w x k : BitString) :
    condContextAssociate (pairCode (pairCode x w) k) =
      pairCode w (pairCode x k) := by
  unfold condContextAssociate
  simp only [decodeFirst_pairCode, decodeSecond_pairCode]

theorem condK_pair_le_add
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ a b z : BitString, ∀ ka kb : ℕ,
      HasPlainConditionalComplexityValue V a z ka →
      HasPlainConditionalComplexityValue V b z kb →
      condK V (pairCode a b) z ≤
        ka + kb + logSlack c (ka + kb + 1) := by
  let splitLength : BitString → Nat := fun q => decodeBits (decodeFirst q)
  let joinedProg : BitString → BitString := fun q => decodeSecond q
  let firstProg : BitString → BitString := fun q => (joinedProg q).take (splitLength q)
  let secondProg : BitString → BitString := fun q => (joinedProg q).drop (splitLength q)
  let D : Map := fun pr =>
    (V (firstProg pr.1, pr.2)).bind fun a =>
      (V (secondProg pr.1, pr.2)).map fun b => pairCode a b
  have hSplitLength : Computable splitLength := decodeBitsComputable.comp decodeFirst_computable
  have hJoinedProg : Computable joinedProg := decodeSecond_computable
  have hFirstProg : Computable firstProg := Primrec.list_take.to_comp.comp hSplitLength hJoinedProg
  have hSecondProg : Computable secondProg :=
    Primrec.list_drop.to_comp.comp hSplitLength hJoinedProg
  have hD : isDecompressor D := by
    have h1 : Partrec (fun pr : BitString × BitString => V (firstProg pr.1, pr.2)) :=
      Partrec.comp hV.1 ((hFirstProg.comp Computable.fst).pair Computable.snd)
    have h2 : Partrec (fun q : (BitString × BitString) × BitString =>
        V (secondProg q.1.1, q.1.2)) :=
      Partrec.comp hV.1
        ((hSecondProg.comp (Computable.fst.comp Computable.fst)).pair
          (Computable.snd.comp Computable.fst))
    have hPair : Computable
        (fun q : ((BitString × BitString) × BitString) × BitString =>
          pairCode q.1.2 q.2) :=
      (show Computable₂ (fun a b : BitString => pairCode a b) from
          pairCode_computable).comp
        (Computable.snd.comp Computable.fst) Computable.snd
    exact Partrec.bind h1 (Partrec.map h2 hPair)
  obtain ⟨cD, hcD⟩ := hV.2 D hD
  refine ⟨cD + 3, fun a b z ka kb ha hb => ?_⟩
  unfold HasPlainConditionalComplexityValue at ha hb
  obtain ⟨pa, hpaLen, hpa⟩ := (condKLeIff V a z ka).mp (le_of_eq ha)
  obtain ⟨pb, hpbLen, hpb⟩ := (condKLeIff V b z kb).mp (le_of_eq hb)
  set prog : BitString := pairCode (Nat.bits pa.length) (pa ++ pb) with hProg
  have hFirstEval : firstProg prog = pa := by
    dsimp [firstProg, joinedProg, splitLength]
    rw [hProg, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits, List.take_left]
  have hSecondEval : secondProg prog = pb := by
    dsimp [secondProg, joinedProg, splitLength]
    rw [hProg, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits, List.drop_left]
  have hDProd : produces D prog z (pairCode a b) := by
    change pairCode a b ∈ (V (firstProg prog, z)).bind fun a =>
      (V (secondProg prog, z)).map fun b => pairCode a b
    rw [hFirstEval, hSecondEval]
    exact Part.mem_bind_iff.mpr ⟨a, hpa, Part.mem_map _ hpb⟩
  have hDBound : condK V (pairCode a b) z ≤ (prog.length : ENat) + (cD : ENat) :=
    (hcD (pairCode a b) z).trans (by gcongr; exact sInf_le ⟨prog, hDProd, rfl⟩)
  have hProgLength : prog.length = 2 * (Nat.bits pa.length).length + pa.length + pb.length + 1 := by
    rw [hProg, length_pairCode, List.length_append]
    omega
  have hpaLen' : pa.length ≤ ka := hpaLen
  have hpbLen' : pb.length ≤ kb := hpbLen
  have hBits : 2 * (Nat.bits pa.length).length ≤ 2 * (Nat.bits (ka + kb + 1)).length := by
    have h1 : pa.length ≤ ka + kb + 1 := by omega
    have h2 := length_natBits_mono h1
    omega
  have hLength : prog.length + cD ≤ ka + kb + logSlack (cD + 3) (ka + kb + 1) := by
    unfold logSlack
    set L := (Nat.bits (ka + kb + 1)).length with hL
    have hexpand : (cD + 3) * L + (cD + 3) = 2 * L + (cD * L + L + cD + 3) := by ring
    rw [hexpand, hProgLength]
    omega
  exact hDBound.trans (by rw [← Nat.cast_add]; exact_mod_cast hLength)

theorem condK_drop_right
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x y w : BitString, ∀ kxy kx : ℕ,
      HasPlainConditionalComplexityValue V (pairCode x y) w kxy →
      HasPlainConditionalComplexityValue V x w kx →
      kx ≤ kxy + c := by
  let D : Map := fun pr =>
    (V (pr.1, pr.2)).map fun p => decodeFirst p
  have hD : isDecompressor D := by
    have h1 : Partrec (fun pr : BitString × BitString => V (pr.1, pr.2)) := hV.1
    exact Partrec.map h1 (decodeFirst_computable.comp Computable.snd)
  obtain ⟨cD, hcD⟩ := hV.2 D hD
  refine ⟨cD, fun x y w kxy kx hxy hx => ?_⟩
  unfold HasPlainConditionalComplexityValue at hx hxy
  obtain ⟨pxy, hpxyLen, hpxy⟩ := (condKLeIff V (pairCode x y) w kxy).mp (le_of_eq hxy)
  have hDProd : produces D pxy w x := by
    change x ∈ (V (pxy, w)).map fun p => decodeFirst p
    have : x = decodeFirst (pairCode x y) := (decodeFirst_pairCode x y).symm
    rw [this]
    exact Part.mem_map _ hpxy
  have hDBound : condK V x w ≤ (pxy.length : ENat) + (cD : ENat) :=
    (hcD x w).trans (by gcongr; exact sInf_le ⟨pxy, hDProd, rfl⟩)
  have hDBound' : (kx : ENat) ≤ (kxy : ENat) + (cD : ENat) := by
    calc
      (kx : ENat) = condK V x w := hx.symm
      _ ≤ (pxy.length : ENat) + (cD : ENat) := hDBound
      _ ≤ (kxy : ENat) + (cD : ENat) := by gcongr
  exact_mod_cast hDBound'


/-- Lower chain direction for plain conditional complexity, with a constant
uniform in the external condition `w`. -/
theorem condK_pairCode_chain_lower_values
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x y w : BitString, ∀ kx kyx kxy : ℕ,
      HasPlainConditionalComplexityValue V x w kx →
      HasPlainConditionalComplexityValue V y (pairCode x w) kyx →
      HasPlainConditionalComplexityValue V (pairCode x y) w kxy →
      kx + kyx ≤ kxy + logSlack c (kxy + 1) := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨cPlain, hPlain⟩ := condK_le_KP V U hV hU.isPrefixDecompressor
  obtain ⟨cRemove, hRemove⟩ := KP_cond_remove_short_info U hU
  obtain ⟨cAssoc, hAssoc⟩ :=
    KP_cond_map_le U hU condContextAssociate condContextAssociate_computable
  obtain ⟨cLower, hLower⟩ := KPCondPair_chain_lower U hU
  obtain ⟨cPair, hPair⟩ := KP_le_condK_add_log_of_value U V hU hV
  obtain ⟨cNat, hNat⟩ := KPPlain_natCode_le_log U hU
  obtain ⟨cProj, hProj⟩ := KP_map_le U hU decodeFirst decodeFirst_computable
  let cNatRaw := 2 + cNat
  obtain ⟨cNatFold, hNatFold⟩ := logSlack_fold_level cNatRaw cPair
  let cNatTotal := cNatFold + logSlack cNatFold cProj
  let cFixed := 2 * cPlain + cRemove + cAssoc + cLower
  let C := cPair + cNatTotal + cFixed
  refine ⟨C, fun x y w kx kyx kxy hx hyx hxy => ?_⟩
  have hkpxFinite : KP U x w ≠ ⊤ := by
    have h := hPair x w kx hx
    refine ne_top_of_le_ne_top ?_ h
    rw [← Nat.cast_add]
    exact ENat.coe_ne_top _
  obtain ⟨kpx, hkpx⟩ := ENat.ne_top_iff_exists.mp hkpxFinite
  have hkpxValue : HasCondPrefixComplexityValue U x w kpx := hkpx
  have hkpxBoundENat :
      (kpx : ENat) ≤
        (kxy : ENat) + (logSlack cPair (kxy + 1) : ENat) + (cProj : ENat) := by
    calc
      (kpx : ENat) = KP U x w := hkpx
      _ ≤ KP U (pairCode x y) w + (cProj : ENat) := by
        simpa only [decodeFirst_pairCode] using hProj (pairCode x y) w
      _ ≤ ((kxy : ENat) + (logSlack cPair (kxy + 1) : ENat)) +
          (cProj : ENat) := by
        gcongr
        exact hPair (pairCode x y) w kxy hxy
  have hkpxBound :
      kpx ≤ (kxy + 1) + cProj + logSlack cPair (kxy + 1) := by
    have hnat : kpx ≤ kxy + logSlack cPair (kxy + 1) + cProj := by
      exact_mod_cast hkpxBoundENat
    omega
  have hNatRaw :
      2 * (Nat.bits kpx).length + cNat ≤ logSlack cNatRaw kpx := by
    dsimp [cNatRaw]
    unfold logSlack
    nlinarith [Nat.zero_le (cNat * (Nat.bits kpx).length)]
  have hNatFolded :
      2 * (Nat.bits kpx).length + cNat ≤
        logSlack cNatTotal (kxy + 1) := by
    calc
      2 * (Nat.bits kpx).length + cNat
          ≤ logSlack cNatRaw kpx := hNatRaw
      _ ≤ logSlack cNatFold ((kxy + 1) + 0 + cProj) :=
        hNatFold (kxy + 1) 0 cProj kpx hkpxBound
      _ = logSlack cNatFold (kxy + 1 + cProj) := by simp
      _ ≤ logSlack (cNatFold + logSlack cNatFold cProj) (kxy + 1) := by
        calc
          logSlack cNatFold (kxy + 1 + cProj)
              ≤ logSlack cNatFold (kxy + 1) + logSlack cNatFold cProj :=
            logSlack_add_le cNatFold (kxy + 1) cProj
          _ ≤ logSlack (cNatFold + logSlack cNatFold cProj) (kxy + 1) :=
            logSlack_add_nat_le cNatFold (logSlack cNatFold cProj) (kxy + 1)
  have hOverhead :
      logSlack cPair (kxy + 1) +
          (2 * (Nat.bits kpx).length + cNat) + cFixed ≤
        logSlack C (kxy + 1) := by
    calc
      logSlack cPair (kxy + 1) +
            (2 * (Nat.bits kpx).length + cNat) + cFixed
          ≤ logSlack cPair (kxy + 1) +
              logSlack cNatTotal (kxy + 1) + cFixed := by
        dsimp [cNatTotal] at hNatFolded ⊢
        omega
      _ = logSlack (cPair + cNatTotal) (kxy + 1) + cFixed := by
        rw [logSlack_add_const]
      _ ≤ logSlack C (kxy + 1) := by
        simpa [C] using
          logSlack_add_nat_le (cPair + cNatTotal) cFixed (kxy + 1)
  have hMain : ((kx + kyx : Nat) : ENat) ≤
      ((kxy + logSlack C (kxy + 1) : Nat) : ENat) := by
    calc
      ((kx + kyx : Nat) : ENat) = (kx : ENat) + (kyx : ENat) := by
        rw [Nat.cast_add]
      _ ≤ (KP U x w + (cPlain : ENat)) +
          (KP U y (pairCode x w) + (cPlain : ENat)) := by
        gcongr
        · rw [← hx]
          exact hPlain x w
        · rw [← hyx]
          exact hPlain y (pairCode x w)
      _ ≤ (KP U x w + (cPlain : ENat)) +
          (KP U y (pairCode (pairCode x w) (natCode kpx)) +
            KPPlain U (natCode kpx) + (cRemove : ENat) + (cPlain : ENat)) := by
        gcongr
        exact hRemove y (pairCode x w) (natCode kpx)
      _ ≤ (KP U x w + (cPlain : ENat)) +
          ((KP U y (prefixCondComplexityContext w x kpx) + (cAssoc : ENat)) +
            KPPlain U (natCode kpx) + (cRemove : ENat) + (cPlain : ENat)) := by
        gcongr
        simp only [prefixCondComplexityContext]
        have h := hAssoc y (pairCode (pairCode x w) (natCode kpx))
        rw [condContextAssociate_pairCode] at h
        exact @le_of_eq_of_le ℕ∞ _ _ _ instPreorderENat.toLE rfl h
      _ = (KP U x w + KP U y (prefixCondComplexityContext w x kpx)) +
          KPPlain U (natCode kpx) +
          ((2 * cPlain + cRemove + cAssoc : Nat) : ENat) := by
        push_cast
        ring
      _ ≤ (KPCondPair U x y w + (cLower : ENat)) +
          KPPlain U (natCode kpx) +
          ((2 * cPlain + cRemove + cAssoc : Nat) : ENat) := by
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_right
            (add_le_add_right (hLower x y w kpx hkpxValue) (KPPlain U (natCode kpx)))
            ((2 * cPlain + cRemove + cAssoc : Nat) : ENat)
      _ ≤ (((kxy : ENat) + (logSlack cPair (kxy + 1) : ENat)) +
            (cLower : ENat)) +
          (2 * (Nat.bits kpx).length + (cNat : ENat)) +
          ((2 * cPlain + cRemove + cAssoc : Nat) : ENat) := by
        gcongr
        · exact hPair (pairCode x y) w kxy hxy
        · exact hNat kpx
      _ = ((kxy +
          (logSlack cPair (kxy + 1) +
            (2 * (Nat.bits kpx).length + cNat) + cFixed) : Nat) : ENat) := by
        dsimp [cFixed]
        push_cast
        ring
      _ ≤ ((kxy + logSlack C (kxy + 1) : Nat) : ENat) := by
        apply ENat.coe_le_coe.mpr
        exact Nat.add_le_add_left hOverhead kxy
  exact ENat.coe_le_coe.mp hMain

/-- Upper chain direction for plain conditional complexity, uniform in `w`. -/
theorem condK_pairCode_chain_upper_values
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x y w : BitString, ∀ kx kyx kxy : ℕ,
      HasPlainConditionalComplexityValue V x w kx →
      HasPlainConditionalComplexityValue V y (pairCode x w) kyx →
      HasPlainConditionalComplexityValue V (pairCode x y) w kxy →
      kxy ≤ kx + kyx + logSlack c (kxy + 1) := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨cPair, hPair⟩ := condK_le_KP V U hV hU.isPrefixDecompressor
  obtain ⟨cChain, hChain⟩ := KPCondPair_chain_upper U hU
  obtain ⟨cCond, hCond⟩ := KP_le_condK_add_log_of_value U V hU hV
  obtain ⟨cDropPrefix, hDropPrefix⟩ := KP_cond_drop_right_le U hU
  obtain ⟨cReassoc, hReassoc⟩ :=
    KP_cond_map_le U hU condContextReassociate condContextReassociate_computable
  obtain ⟨cDropRight, hDropRight⟩ := condK_drop_right V hV
  obtain ⟨cDropLeft, hDropLeft⟩ := condK_drop_left V hV
  obtain ⟨cAddCond, hAddCond⟩ := condK_condPair_right_le V hV
  obtain ⟨cLogs, hLogs⟩ :=
    logSlack_two_values_le_pair cCond cCond cDropRight (cDropLeft + cAddCond)
  let cFixed := cDropPrefix + cReassoc + cChain + cPair
  let C := cLogs + cFixed
  refine ⟨C, fun x y w kx kyx kxy hx hyx hxy => ?_⟩
  have hkpxFinite : KP U x w ≠ ⊤ := by
    have h := hCond x w kx hx
    refine ne_top_of_le_ne_top ?_ h
    rw [← Nat.cast_add]
    exact ENat.coe_ne_top _
  obtain ⟨kpx, hkpx⟩ := ENat.ne_top_iff_exists.mp hkpxFinite
  have hkpxValue : HasCondPrefixComplexityValue U x w kpx := hkpx
  have hkxBound : kx ≤ kxy + cDropRight :=
    hDropRight x y w kxy kx hxy hx
  have hkyxBoundENat :
      (kyx : ENat) ≤ (kxy : ENat) + (cDropLeft + cAddCond : Nat) := by
    calc
      (kyx : ENat) = condK V y (pairCode x w) := hyx.symm
      _ ≤ condK V y w + (cAddCond : ENat) := hAddCond y x w
      _ ≤ (condK V (pairCode x y) w + (cDropLeft : ENat)) +
          (cAddCond : ENat) := by
        gcongr
        have hproj := hDropLeft x y w kxy
        obtain ⟨kyw, hkyw⟩ := exists_plainConditionalComplexityValue V hV y w
        have hnat := hproj kyw hxy hkyw
        rw [hxy, hkyw]
        exact_mod_cast hnat
      _ = (kxy : ENat) + (cDropLeft + cAddCond : Nat) := by
        rw [hxy]
        push_cast
        ring
  have hkyxBound : kyx ≤ kxy + (cDropLeft + cAddCond) := by
    exact_mod_cast hkyxBoundENat
  have hTwoLogs :
      logSlack cCond (kx + 1) + logSlack cCond (kyx + 1) ≤
        logSlack cLogs (kxy + 1) :=
    hLogs kx kyx kxy hkxBound (by omega)
  have hOverhead :
      logSlack cCond (kx + 1) + logSlack cCond (kyx + 1) + cFixed ≤
        logSlack C (kxy + 1) := by
    calc
      logSlack cCond (kx + 1) + logSlack cCond (kyx + 1) + cFixed
          ≤ logSlack cLogs (kxy + 1) + cFixed := Nat.add_le_add_right hTwoLogs _
      _ ≤ logSlack C (kxy + 1) := by
        simpa [C] using logSlack_add_nat_le cLogs cFixed (kxy + 1)
  have hyPrefix :
      KP U y (prefixCondComplexityContext w x kpx) ≤
        (kyx : ENat) + (logSlack cCond (kyx + 1) : ENat) +
          (cDropPrefix + cReassoc : Nat) := by
    calc
      KP U y (prefixCondComplexityContext w x kpx)
          ≤ KP U y (condContextReassociate
              (prefixCondComplexityContext w x kpx)) + (cReassoc : ENat) :=
        hReassoc y (prefixCondComplexityContext w x kpx)
      _ = KP U y (pairCode (pairCode x w) (natCode kpx)) +
          (cReassoc : ENat) := by rw [condContextReassociate_prefixCondComplexityContext]
      _ ≤ (KP U y (pairCode x w) + (cDropPrefix : ENat)) +
          (cReassoc : ENat) := by
        gcongr
        exact hDropPrefix y (pairCode x w) (natCode kpx)
      _ ≤ (((kyx : ENat) + (logSlack cCond (kyx + 1) : ENat)) +
          (cDropPrefix : ENat)) + (cReassoc : ENat) := by
        gcongr
        exact hCond y (pairCode x w) kyx hyx
      _ = (kyx : ENat) + (logSlack cCond (kyx + 1) : ENat) +
          (cDropPrefix + cReassoc : Nat) := by push_cast; ring
  have hMain : (kxy : ENat) ≤
      ((kx + kyx + logSlack C (kxy + 1) : Nat) : ENat) := by
    calc
      (kxy : ENat) = condK V (pairCode x y) w := hxy.symm
      _ ≤ KP U (pairCode x y) w + (cPair : ENat) := hPair (pairCode x y) w
      _ = KPCondPair U x y w + (cPair : ENat) := rfl
      _ ≤ (KP U x w + KP U y (prefixCondComplexityContext w x kpx) +
          (cChain : ENat)) + (cPair : ENat) := by
        gcongr
        exact hChain x y w kpx hkpxValue
      _ ≤ (((kx : ENat) + (logSlack cCond (kx + 1) : ENat)) +
            ((kyx : ENat) + (logSlack cCond (kyx + 1) : ENat) +
              (cDropPrefix + cReassoc : Nat)) + (cChain : ENat)) +
          (cPair : ENat) := by
        gcongr
        · exact hCond x w kx hx
      _ = ((kx + kyx +
          (logSlack cCond (kx + 1) + logSlack cCond (kyx + 1) + cFixed) : Nat) : ENat) := by
        dsimp [cFixed]
        push_cast
        ring
      _ ≤ ((kx + kyx + logSlack C (kxy + 1) : Nat) : ENat) := by
        apply ENat.coe_le_coe.mpr
        exact Nat.add_le_add_left hOverhead (kx + kyx)
  exact ENat.coe_le_coe.mp hMain

theorem condK_pairCode_symmetryOfInformation_values
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x y w : BitString, ∀ kx kyx kxy : ℕ,
      HasPlainConditionalComplexityValue V x w kx →
      HasPlainConditionalComplexityValue V y (pairCode x w) kyx →
      HasPlainConditionalComplexityValue V (pairCode x y) w kxy →
      (kxy ≤ kx + kyx + logSlack c (kxy + 1)) ∧
      (kx + kyx ≤ kxy + logSlack c (kxy + 1)) := by
  obtain ⟨cUpper, hUpper⟩ := condK_pairCode_chain_upper_values V hV
  obtain ⟨cLower, hLower⟩ := condK_pairCode_chain_lower_values V hV
  refine ⟨cUpper + cLower, ?_⟩
  intro x y w kx kyx kxy hx hyx hxy
  constructor
  · exact (hUpper x y w kx kyx kxy hx hyx hxy).trans
      (Nat.add_le_add_left
        (logSlack_mono_left (Nat.le_add_right cUpper cLower) (kxy + 1))
        (kx + kyx))
  · exact (hLower x y w kx kyx kxy hx hyx hxy).trans
      (Nat.add_le_add_left
        (logSlack_mono_left (Nat.le_add_left cLower cUpper) (kxy + 1)) kxy)

/-- Swap the two components of a canonical pair code. -/
def swapPairCode (q : BitString) : BitString :=
  pairCode (decodeSecond q) (decodeFirst q)

theorem swapPairCode_computable : Computable swapPairCode := by
  have h : swapPairCode =
      (fun p : BitString × BitString => pairCode p.1 p.2) ∘
        (fun q : BitString => (decodeSecond q, decodeFirst q)) := by
    funext q
    rfl
  rw [h]
  exact pairCode_computable.comp (decodeSecond_computable.pair decodeFirst_computable)

@[simp] theorem swapPairCode_pairCode (x y : BitString) :
    swapPairCode (pairCode x y) = pairCode y x := by
  unfold swapPairCode
  rw [decodeSecond_pairCode, decodeFirst_pairCode]

/-- Conditional complexity is invariant under swapping a pair code, in the
one direction needed below. Applying the theorem twice gives the converse. -/
theorem condK_swapPairCode_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x y w : BitString,
      condK V (pairCode y x) w ≤ condK V (pairCode x y) w + (c : ENat) := by
  obtain ⟨c, hc⟩ := condKMapLe V hV swapPairCode swapPairCode_computable
  refine ⟨c, fun x y w => ?_⟩
  simpa using hc (pairCode x y) w

/-- Kolmogorov submodularity for two pairs sharing a component:
`C(z|w) + C(a,b|w) ≤ C(a,z|w) + C(b,z|w) + O(log)`.

The proof exposes the exact mechanism: conditional symmetry of information at
`z`, conditional pair coding for `(a,b)` given `z,w`, projection of the triple,
and computable pair-order swaps. -/
theorem condK_pairCode_submodularity_values
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ (a b z w : BitString) (kzw kabw kazw kbzw : ℕ),
      HasPlainConditionalComplexityValue V z w kzw →
      HasPlainConditionalComplexityValue V (pairCode a b) w kabw →
      HasPlainConditionalComplexityValue V (pairCode a z) w kazw →
      HasPlainConditionalComplexityValue V (pairCode b z) w kbzw →
      kzw + kabw ≤ kazw + kbzw +
        logSlack C (kzw + kabw + kazw + kbzw + 1) := by
  obtain ⟨cSoI, hSoI⟩ := condK_pairCode_symmetryOfInformation_values V hV
  obtain ⟨cPair, hPair⟩ := condK_pair_le_add V hV
  obtain ⟨cDrop, hDrop⟩ := condK_drop_right V hV
  obtain ⟨cSwap, hSwap⟩ := condK_swapPairCode_le V hV
  obtain ⟨bSoI, hbSoI⟩ := logSlack_le_add_const cSoI
  obtain ⟨bPair, hbPair⟩ := logSlack_le_add_const cPair
  let cRaw := cSoI + cPair
  let B := 4 * cSwap + 4 * bSoI + 2 * bPair + 10
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cRaw 8 B
  let C := 4 * cFold + (3 * cSwap + cDrop)
  refine ⟨C, fun a b z w kzw kabw kazw kbzw hzw habw hazw hbzw => ?_⟩
  obtain ⟨kzaw, hzaw⟩ :=
    exists_plainConditionalComplexityValue V hV (pairCode z a) w
  obtain ⟨kzbw, hzbw⟩ :=
    exists_plainConditionalComplexityValue V hV (pairCode z b) w
  obtain ⟨kazc, hazc⟩ :=
    exists_plainConditionalComplexityValue V hV a (pairCode z w)
  obtain ⟨kbzc, hbzc⟩ :=
    exists_plainConditionalComplexityValue V hV b (pairCode z w)
  obtain ⟨kabzc, habzc⟩ :=
    exists_plainConditionalComplexityValue V hV (pairCode a b) (pairCode z w)
  obtain ⟨kzabw, hzabw⟩ :=
    exists_plainConditionalComplexityValue V hV (pairCode z (pairCode a b)) w
  obtain ⟨kabzw, habzw⟩ :=
    exists_plainConditionalComplexityValue V hV (pairCode (pairCode a b) z) w
  have hza := hSoI z a w kzw kazc kzaw hzw hazc hzaw
  have hzb := hSoI z b w kzw kbzc kzbw hzw hbzc hzbw
  have hzabChain := hSoI z (pairCode a b) w kzw kabzc kzabw hzw habzc hzabw
  have habGivenZ_ENat := hPair a b (pairCode z w) kazc kbzc hazc hbzc
  have habGivenZ :
      kabzc ≤ kazc + kbzc + logSlack cPair (kazc + kbzc + 1) := by
    rw [habzc] at habGivenZ_ENat
    exact_mod_cast habGivenZ_ENat
  have hTripleDirect_ENat := hPair z (pairCode a b) w kzw kabw hzw habw
  have hTripleDirect :
      kzabw ≤ kzw + kabw + logSlack cPair (kzw + kabw + 1) := by
    rw [hzabw] at hTripleDirect_ENat
    exact_mod_cast hTripleDirect_ENat
  have hDropNat : kabw ≤ kabzw + cDrop :=
    hDrop (pairCode a b) z w kabzw kabw habzw habw
  have hSwapTriple_ENat := hSwap z (pairCode a b) w
  have hSwapTriple : kabzw ≤ kzabw + cSwap := by
    rw [habzw, hzabw] at hSwapTriple_ENat
    exact_mod_cast hSwapTriple_ENat
  have hSwapA_ENat := hSwap a z w
  have hSwapA : kzaw ≤ kazw + cSwap := by
    rw [hzaw, hazw] at hSwapA_ENat
    exact_mod_cast hSwapA_ENat
  have hSwapB_ENat := hSwap b z w
  have hSwapB : kzbw ≤ kbzw + cSwap := by
    rw [hzbw, hbzw] at hSwapB_ENat
    exact_mod_cast hSwapB_ENat
  set BIG := kzw + kabw + kazw + kbzw with hBIG
  set Sza := logSlack cSoI (kzaw + 1) with hSza
  set Szb := logSlack cSoI (kzbw + 1) with hSzb
  set Szab := logSlack cSoI (kzabw + 1) with hSzab
  set Spair := logSlack cPair (kazc + kbzc + 1) with hSpair
  have hArgZa : kzaw + 1 ≤ 8 * (BIG + 1) + B := by
    dsimp [BIG, B]
    omega
  have hArgZb : kzbw + 1 ≤ 8 * (BIG + 1) + B := by
    dsimp [BIG, B]
    omega
  have hArgZab : kzabw + 1 ≤ 8 * (BIG + 1) + B := by
    have hlog := hbPair (kzw + kabw + 1)
    dsimp [BIG, B]
    omega
  have hKazc : kazc ≤ kzaw + logSlack cSoI (kzaw + 1) := by omega
  have hKbzc : kbzc ≤ kzbw + logSlack cSoI (kzbw + 1) := by omega
  have hArgPair : kazc + kbzc + 1 ≤ 8 * (BIG + 1) + B := by
    have hlogA := hbSoI (kzaw + 1)
    have hlogB := hbSoI (kzbw + 1)
    dsimp [BIG, B]
    omega
  have foldOne : ∀ c arg : ℕ, c ≤ cRaw →
      arg ≤ 8 * (BIG + 1) + B →
      logSlack c arg ≤ logSlack cFold (BIG + 1) := by
    intro c arg hc harg
    calc
      logSlack c arg ≤ logSlack cRaw arg := logSlack_mono_left hc arg
      _ ≤ logSlack cRaw (8 * (BIG + 1) + B) := logSlack_mono_right cRaw harg
      _ ≤ logSlack cFold (BIG + 1) := hFold (BIG + 1)
  have hSzaFold : Sza ≤ logSlack cFold (BIG + 1) := by
    rw [hSza]
    exact foldOne cSoI (kzaw + 1) (Nat.le_add_right _ _) hArgZa
  have hSzbFold : Szb ≤ logSlack cFold (BIG + 1) := by
    rw [hSzb]
    exact foldOne cSoI (kzbw + 1) (Nat.le_add_right _ _) hArgZb
  have hSzabFold : Szab ≤ logSlack cFold (BIG + 1) := by
    rw [hSzab]
    exact foldOne cSoI (kzabw + 1) (Nat.le_add_right _ _) hArgZab
  have hSpairFold : Spair ≤ logSlack cFold (BIG + 1) := by
    rw [hSpair]
    exact foldOne cPair (kazc + kbzc + 1) (Nat.le_add_left _ _) hArgPair
  have hSlack :
      Sza + Szb + Szab + Spair + (3 * cSwap + cDrop) ≤
        logSlack C (BIG + 1) := by
    calc
      Sza + Szb + Szab + Spair + (3 * cSwap + cDrop)
          ≤ 4 * logSlack cFold (BIG + 1) + (3 * cSwap + cDrop) := by omega
      _ = logSlack (4 * cFold) (BIG + 1) + (3 * cSwap + cDrop) := by
        rw [logSlack_nsmul]
      _ ≤ logSlack C (BIG + 1) := by
        simpa [C] using
          logSlack_add_nat_le (4 * cFold) (3 * cSwap + cDrop) (BIG + 1)
  have hCore : kzw + kabw ≤ kazw + kbzw +
      (Sza + Szb + Szab + Spair + (3 * cSwap + cDrop)) := by
    omega
  rw [hBIG] at hSlack
  exact hCore.trans (Nat.add_le_add_left hSlack (kazw + kbzw))

/-- **Base inequality (SUV Problem 296 / p. 362), relativized to a context `w`,
in subtraction-free form.**

`C(z|w) + C(a,b|w) ≤ C(z|a,w) + C(z|b,w) + C(a|w) + C(b|w) + O(log)`, i.e. the
complexity form of `H(t) ≤ H(t|α) + H(t|β) + I(α:β)`.

The proof uses the conditional submodularity theorem above and the two chain
upper bounds for `(a,z)` and `(b,z)`. -/
theorem base_conditional_mutualInformation_inequality
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ (z a b w : BitString) (kzw kabw kzaw kzbw kaw kbw : ℕ),
      HasPlainConditionalComplexityValue V z w kzw →
      HasPlainConditionalComplexityValue V (pairCode a b) w kabw →
      HasPlainConditionalComplexityValue V z (pairCode a w) kzaw →
      HasPlainConditionalComplexityValue V z (pairCode b w) kzbw →
      HasPlainConditionalComplexityValue V a w kaw →
      HasPlainConditionalComplexityValue V b w kbw →
      kzw + kabw ≤
        kzaw + kzbw + kaw + kbw +
          logSlack C (kzw + kabw + kzaw + kzbw + kaw + kbw + 1) := by
  obtain ⟨cSub, hSub⟩ := condK_pairCode_submodularity_values V hV
  obtain ⟨cSoI, hSoI⟩ := condK_pairCode_symmetryOfInformation_values V hV
  obtain ⟨cPair, hPair⟩ := condK_pair_le_add V hV
  obtain ⟨bPair, hbPair⟩ := logSlack_le_add_const cPair
  let cRaw := cSub + cSoI
  let B := 2 * bPair + 4
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cRaw 6 B
  let C := 3 * cFold
  refine ⟨C, fun z a b w kzw kabw kzaw kzbw kaw kbw
    hzw habw hzaw hzbw haw hbw => ?_⟩
  obtain ⟨kazw, hazw⟩ :=
    exists_plainConditionalComplexityValue V hV (pairCode a z) w
  obtain ⟨kbzw, hbzw⟩ :=
    exists_plainConditionalComplexityValue V hV (pairCode b z) w
  have hSubInst := hSub a b z w kzw kabw kazw kbzw hzw habw hazw hbzw
  have hSoIA := hSoI a z w kaw kzaw kazw haw hzaw hazw
  have hSoIB := hSoI b z w kbw kzbw kbzw hbw hzbw hbzw
  have hPairA_ENat := hPair a z w kaw kzw haw hzw
  have hPairA :
      kazw ≤ kaw + kzw + logSlack cPair (kaw + kzw + 1) := by
    rw [hazw] at hPairA_ENat
    exact_mod_cast hPairA_ENat
  have hPairB_ENat := hPair b z w kbw kzw hbw hzw
  have hPairB :
      kbzw ≤ kbw + kzw + logSlack cPair (kbw + kzw + 1) := by
    rw [hbzw] at hPairB_ENat
    exact_mod_cast hPairB_ENat
  set BIG := kzw + kabw + kzaw + kzbw + kaw + kbw with hBIG
  set Ssub := logSlack cSub (kzw + kabw + kazw + kbzw + 1) with hSsub
  set Sa := logSlack cSoI (kazw + 1) with hSa
  set Sb := logSlack cSoI (kbzw + 1) with hSb
  have hArgA : kazw + 1 ≤ 6 * (BIG + 1) + B := by
    have hlog := hbPair (kaw + kzw + 1)
    dsimp [BIG, B]
    omega
  have hArgB : kbzw + 1 ≤ 6 * (BIG + 1) + B := by
    have hlog := hbPair (kbw + kzw + 1)
    dsimp [BIG, B]
    omega
  have hArgSub :
      kzw + kabw + kazw + kbzw + 1 ≤ 6 * (BIG + 1) + B := by
    have hlogA := hbPair (kaw + kzw + 1)
    have hlogB := hbPair (kbw + kzw + 1)
    dsimp [BIG, B]
    omega
  have foldOne : ∀ c arg : ℕ, c ≤ cRaw →
      arg ≤ 6 * (BIG + 1) + B →
      logSlack c arg ≤ logSlack cFold (BIG + 1) := by
    intro c arg hc harg
    calc
      logSlack c arg ≤ logSlack cRaw arg := logSlack_mono_left hc arg
      _ ≤ logSlack cRaw (6 * (BIG + 1) + B) := logSlack_mono_right cRaw harg
      _ ≤ logSlack cFold (BIG + 1) := hFold (BIG + 1)
  have hSsubFold : Ssub ≤ logSlack cFold (BIG + 1) := by
    rw [hSsub]
    exact foldOne cSub _ (Nat.le_add_right _ _) hArgSub
  have hSaFold : Sa ≤ logSlack cFold (BIG + 1) := by
    rw [hSa]
    exact foldOne cSoI _ (Nat.le_add_left _ _) hArgA
  have hSbFold : Sb ≤ logSlack cFold (BIG + 1) := by
    rw [hSb]
    exact foldOne cSoI _ (Nat.le_add_left _ _) hArgB
  have hSlack : Ssub + Sa + Sb ≤ logSlack C (BIG + 1) := by
    calc
      Ssub + Sa + Sb ≤ 3 * logSlack cFold (BIG + 1) := by omega
      _ = logSlack C (BIG + 1) := by
        dsimp [C]
        rw [logSlack_nsmul]
  have hCore : kzw + kabw ≤
      kzaw + kzbw + kaw + kbw + (Ssub + Sa + Sb) := by
    omega
  rw [hBIG] at hSlack
  exact hCore.trans
    (Nat.add_le_add_left hSlack (kzaw + kzbw + kaw + kbw))

/-- `logSlack` is additive in its constant at a fixed argument. -/
theorem logSlack_add_same (a b n : ℕ) :
    logSlack a n + logSlack b n = logSlack (a + b) n := by
  unfold logSlack; ring

/-- **SUV Theorem 228.** For arbitrary strings `x, y, z, u, v`,
```
C(z) ≤ 2·C(z|x) + 2·C(z|y) + I(x:y|u) + I(x:y|v) + I(u:v)
```
with `O(log)` precision.  Stated in exact, subtraction-free values form:
```
C(z) + C(x,y|u) + C(x,y|v) + C(u,v)
  ≤ 2·C(z|x) + 2·C(z|y) + C(x|u) + C(y|u) + C(x|v) + C(y|v) + C(u) + C(v) + logSlack C (…).
```
-/
theorem theorem_228_conditional_independence_bound
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ (x y z u v : BitString)
      (kz kzx kzy kxu kyu kxv kyv ku kv kxyu kxyv kuv : ℕ),
      HasPlainComplexityValue V z kz →
      HasPlainConditionalComplexityValue V z x kzx →
      HasPlainConditionalComplexityValue V z y kzy →
      HasPlainConditionalComplexityValue V x u kxu →
      HasPlainConditionalComplexityValue V y u kyu →
      HasPlainConditionalComplexityValue V x v kxv →
      HasPlainConditionalComplexityValue V y v kyv →
      HasPlainComplexityValue V u ku →
      HasPlainComplexityValue V v kv →
      HasPlainConditionalComplexityValue V (pairCode x y) u kxyu →
      HasPlainConditionalComplexityValue V (pairCode x y) v kxyv →
      HasPlainComplexityValue V (pairCode u v) kuv →
      kz + kxyu + kxyv + kuv ≤
        2 * kzx + 2 * kzy + kxu + kyu + kxv + kyv + ku + kv +
          logSlack C (kz + kzx + kzy + kxu + kyu + kxv + kyv + ku + kv
            + kxyu + kxyv + kuv + 1) := by
  classical
  obtain ⟨Cbase, hbase⟩ := base_conditional_mutualInformation_inequality V hV
  obtain ⟨cmono, hmono⟩ := condK_condPair_left_le V hV
  obtain ⟨c0, hc0⟩ := condKLePlainK V hV
  -- Fold constant for the three base-inequality slacks.
  obtain ⟨Cfold, hfold⟩ := logSlack_linear_bound Cbase 6 (3 * (c0 + cmono) + 1)
  refine ⟨6 * cmono + 3 * Cfold, ?_⟩
  intro x y z u v kz kzx kzy kxu kyu kxv kyv ku kv kxyu kxyv kuv
    hz hzx hzy hxu hyu hxv hyv hu hv hxyu hxyv hkuv
  -- Condition monotonicity, in value form.
  have monoNat : ∀ (w s t : BitString) (kwst kws : ℕ),
      HasPlainConditionalComplexityValue V w (pairCode s t) kwst →
      HasPlainConditionalComplexityValue V w s kws →
      kwst ≤ kws + cmono := by
    intro w s t kwst kws h1 h2
    have h := hmono w s t
    unfold HasPlainConditionalComplexityValue at h1 h2
    rw [h1, h2] at h
    have h' : (kwst : ENat) ≤ ((kws + cmono : ℕ) : ENat) := by rwa [Nat.cast_add]
    exact_mod_cast h'
  -- Conditioning cannot increase complexity beyond the unconditional value.
  have leplainNat : ∀ (w s : BitString) (kws kw : ℕ),
      HasPlainConditionalComplexityValue V w s kws →
      HasPlainComplexityValue V w kw →
      kws ≤ kw + c0 := by
    intro w s kws kw h1 h2
    have h := hc0 w s
    unfold HasPlainConditionalComplexityValue at h1
    unfold HasPlainComplexityValue at h2
    rw [h1, h2] at h
    have h' : (kws : ENat) ≤ ((kw + c0 : ℕ) : ENat) := by rwa [Nat.cast_add]
    exact_mod_cast h'
  -- Intermediate exact values.
  obtain ⟨kzu, hkzu⟩ := exists_plainConditionalComplexityValue V hV z u
  obtain ⟨kzv, hkzv⟩ := exists_plainConditionalComplexityValue V hV z v
  obtain ⟨kzuNil, hkzuNil⟩ :=
    exists_plainConditionalComplexityValue V hV z (pairCode u [])
  obtain ⟨kzvNil, hkzvNil⟩ :=
    exists_plainConditionalComplexityValue V hV z (pairCode v [])
  obtain ⟨kzxu, hkzxu⟩ := exists_plainConditionalComplexityValue V hV z (pairCode x u)
  obtain ⟨kzyu, hkzyu⟩ := exists_plainConditionalComplexityValue V hV z (pairCode y u)
  obtain ⟨kzxv, hkzxv⟩ := exists_plainConditionalComplexityValue V hV z (pairCode x v)
  obtain ⟨kzyv, hkzyv⟩ := exists_plainConditionalComplexityValue V hV z (pairCode y v)
  -- Base inequality at the three contexts `[]`, `u`, `v`.
  have inst1 := hbase z u v [] kz kuv kzuNil kzvNil ku kv
    (hasCondValue_nil_of_hasPlainValue hz) (hasCondValue_nil_of_hasPlainValue hkuv)
    hkzuNil hkzvNil
    (hasCondValue_nil_of_hasPlainValue hu) (hasCondValue_nil_of_hasPlainValue hv)
  have inst2 := hbase z x y u kzu kxyu kzxu kzyu kxu kyu
    hkzu hxyu hkzxu hkzyu hxu hyu
  have inst3 := hbase z x y v kzv kxyv kzxv kzyv kxv kyv
    hkzv hxyv hkzxv hkzyv hxv hyv
  -- Abbreviate the three base-slack terms and the visible budget.
  set S1 := logSlack Cbase (kz + kuv + kzuNil + kzvNil + ku + kv + 1) with hS1def
  set S2 := logSlack Cbase (kzu + kxyu + kzxu + kzyu + kxu + kyu + 1) with hS2def
  set S3 := logSlack Cbase (kzv + kxyv + kzxv + kzyv + kxv + kyv + 1) with hS3def
  set BIG := kz + kzx + kzy + kxu + kyu + kxv + kyv + ku + kv + kxyu + kxyv + kuv
    with hBIGdef
  -- The six condition-monotonicity value bounds.
  have m_zuNil := monoNat z u [] kzuNil kzu hkzuNil hkzu
  have m_zvNil := monoNat z v [] kzvNil kzv hkzvNil hkzv
  have m_zxu := monoNat z x u kzxu kzx hkzxu hzx
  have m_zyu := monoNat z y u kzyu kzy hkzyu hzy
  have m_zxv := monoNat z x v kzxv kzx hkzxv hzx
  have m_zyv := monoNat z y v kzyv kzy hkzyv hzy
  have b_zu := leplainNat z u kzu kz hkzu hz
  have b_zv := leplainNat z v kzv kz hkzv hz
  -- Fold each base-slack into the single visible slack.
  have foldSi : ∀ arg : ℕ, arg + 1 ≤ 6 * (BIG + 1) + (3 * (c0 + cmono) + 1) →
      logSlack Cbase (arg + 1) ≤ logSlack Cfold (BIG + 1) := by
    intro arg harg
    calc logSlack Cbase (arg + 1)
        ≤ logSlack Cbase (6 * (BIG + 1) + (3 * (c0 + cmono) + 1)) :=
          logSlack_mono_right Cbase harg
      _ ≤ logSlack Cfold (BIG + 1) := hfold (BIG + 1)
  have hS1le : S1 ≤ logSlack Cfold (BIG + 1) := by
    rw [hS1def]
    exact foldSi (kz + kuv + kzuNil + kzvNil + ku + kv) (by omega)
  have hS2le : S2 ≤ logSlack Cfold (BIG + 1) := by
    rw [hS2def]
    exact foldSi (kzu + kxyu + kzxu + kzyu + kxu + kyu) (by omega)
  have hS3le : S3 ≤ logSlack Cfold (BIG + 1) := by
    rw [hS3def]
    exact foldSi (kzv + kxyv + kzxv + kzyv + kxv + kyv) (by omega)
  have h6 : 6 * cmono ≤ logSlack (6 * cmono) (BIG + 1) := by
    unfold logSlack; exact Nat.le_add_left _ _
  -- Assemble the slack bound.
  have hslack : 6 * cmono + S1 + S2 + S3
      ≤ logSlack (6 * cmono + 3 * Cfold) (BIG + 1) := by
    calc 6 * cmono + S1 + S2 + S3
        ≤ logSlack (6 * cmono) (BIG + 1) + logSlack Cfold (BIG + 1)
            + logSlack Cfold (BIG + 1) + logSlack Cfold (BIG + 1) := by
          have := h6; omega
      _ = logSlack (6 * cmono + 3 * Cfold) (BIG + 1) := by
          simp only [logSlack]; ring
  -- Arithmetic core: combine the three base inequalities and the monotonicities.
  have hcore : kz + kxyu + kxyv + kuv ≤
      2 * kzx + 2 * kzy + kxu + kyu + kxv + kyv + ku + kv
        + (6 * cmono + S1 + S2 + S3) := by
    omega
  omega

/-- **Value-form chain recurrence (arithmetic core of SUV Exercise 316).**

If a sequence of natural numbers `S` satisfies the per-link *doubling* bound
`S (i + 1) ≤ 2 · S i + L` for every link `i < k`, and a top value `T` obeys
`T ≤ S k + L`, then
```
T ≤ 2 ^ k · S 0 + 2 ^ k · L.
```

This is the pure arithmetic backbone of SUV's iterated application of
Theorem 228 along an Exercise-315 conditional-independence chain: taking
`S i = C(z | αᵢ) + C(z | βᵢ)`, `T = C(z)`, and `L` the uniform per-step
logarithmic slack turns the chain of relativized inequalities into the `2 ^ k`
coefficient of Exercise 316.  No coding or complexity notion enters here — the
statement and proof live entirely over `ℕ`, so it is a self-contained,
reusable leaf.  The clean invariant `S m + L ≤ 2 ^ m · (S 0 + L)` (proved by
induction) avoids all truncated subtraction. -/
theorem chain_error_recurrence (k : ℕ) (S : ℕ → ℕ) (T L : ℕ)
    (hstep : ∀ i, i < k → S (i + 1) ≤ 2 * S i + L)
    (htop : T ≤ S k + L) :
    T ≤ 2 ^ k * S 0 + 2 ^ k * L := by
  have key : ∀ m, m ≤ k → S m + L ≤ 2 ^ m * (S 0 + L) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ n ih =>
      intro hm
      have ihn := ih (by omega)
      have hstepn := hstep n (by omega)
      calc S (n + 1) + L
          ≤ 2 * (S n + L) := by omega
        _ ≤ 2 * (2 ^ n * (S 0 + L)) := Nat.mul_le_mul le_rfl ihn
        _ = 2 ^ (n + 1) * (S 0 + L) := by rw [pow_succ]; ring
  have hk := key k le_rfl
  calc T ≤ S k + L := htop
    _ ≤ 2 ^ k * (S 0 + L) := hk
    _ = 2 ^ k * S 0 + 2 ^ k * L := by ring

/-- **Iterated conditional-independence bound (value form, `logSlack` shape).**

Reduction backbone for SUV Exercise 316.  Suppose the per-link value-form
conditional-mutual-information defect satisfies the doubling recurrence
`S (i + 1) ≤ 2 · S i + logSlack C (N + 1)` for every link `i < k` — each such
inequality is what `theorem_228_conditional_independence_bound` /
`base_conditional_mutualInformation_inequality` yield when applied at the
`i`-th link of an Exercise-315 chain — and the top independence bound
`kz ≤ S k + logSlack C (N + 1)` holds.  Then the unconditional value
`kz = C(z)` obeys
```
kz ≤ 2 ^ k · S 0 + logSlack (2 ^ k · C) (N + 1),
```
where `S 0 = C(z | x) + C(z | y)`.

This isolates only the arithmetic assembly.  The per-link defects (`hstep`) and
the top bound (`htop`) are the genuine open obligations, to be discharged by the
fixed-frequency type-log / rank-coding layer; **no** non-extractability
conclusion is assumed as a hypothesis here. -/
theorem iterated_conditional_independence_bound_values
    (k C N kz : ℕ) (S : ℕ → ℕ)
    (hstep : ∀ i, i < k → S (i + 1) ≤ 2 * S i + logSlack C (N + 1))
    (htop : kz ≤ S k + logSlack C (N + 1)) :
    kz ≤ 2 ^ k * S 0 + logSlack (2 ^ k * C) (N + 1) := by
  have h := chain_error_recurrence k S kz (logSlack C (N + 1)) hstep htop
  rwa [logSlack_nsmul (2 ^ k) C (N + 1)] at h

end Kolmogorov
