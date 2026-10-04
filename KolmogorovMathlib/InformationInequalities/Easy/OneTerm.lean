import KolmogorovMathlib.InformationInequalities.Easy.Direction

/-!
# One-term left-hand sides translate into combinatorial inequalities (Problem 283)

SUV Problem 283, p. 317.

A linear inequality between positive combinations of conditional complexities whose left-hand
side is a single term corresponds to a true combinatorial inequality under the translation
`C(x_J | x_I) ↦ log m_A(J | I)` (`logb_maxSection_le_sum_logb_maxSection`).  The proof applies
the complexity inequality to the rows of a power of a maximal section: one row tuple of high
complexity bounds the left-hand side from below, and every section is reconstructed from its
rank among the sections, which bounds each right-hand term from above.
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}

/-! ### One-term left-hand sides translate into combinatorial inequalities -/

private noncomputable def finiteSymbolCode {X : Type} [Fintype X] (x : X) : BitString :=
  Nat.bits (Fintype.equivFin X x).val

private lemma finiteSymbolCode_injective {X : Type} [Fintype X] :
    Function.Injective (finiteSymbolCode : X → BitString) := by
  intro x y h
  apply (Fintype.equivFin X).injective
  apply Fin.ext
  simpa [finiteSymbolCode] using congrArg decodeBits h

private noncomputable def sectionPowerRows {Y : Fin n → Type} [∀ i, Fintype (Y i)]
    [∀ i, DecidableEq (Y i)] (A : Finset (∀ i, Y i)) {N : ℕ}
    (w : Fin N → {a // a ∈ A}) : Fin n → BitString :=
  fun i => listCode (List.ofFn fun t => finiteSymbolCode ((w t).val i))

private lemma exists_sectionPowerRows_length_bound {Y : Fin n → Type}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] (A : Finset (∀ i, Y i)) :
    ∃ a : ℕ, ∀ (N : ℕ) (w : Fin N → {a // a ∈ A}),
      tupleMaxLength (sectionPowerRows A w) ≤ a * N + a := by
  let a := Finset.univ.sup fun i : Fin n => 2 * Fintype.card (Y i) + 1
  refine ⟨a, fun N w => ?_⟩
  have hcode : ∀ (L : List BitString) (b : ℕ),
      (∀ x ∈ L, x.length ≤ b) → (listCode L).length ≤ L.length * (2 * b + 1) := by
    intro L b hL
    induction L with
    | nil => simp
    | cons x L ih =>
        rw [length_listCode_cons]
        have hx := hL x (by simp)
        have htail := ih (fun y hy => hL y (by simp [hy]))
        simp only [List.length_cons]
        calc
          2 * x.length + 1 + (listCode L).length ≤
              (2 * b + 1) + L.length * (2 * b + 1) :=
            Nat.add_le_add (by omega) htail
          _ = (L.length + 1) * (2 * b + 1) := by ring
  unfold tupleMaxLength
  refine Finset.sup_le fun i _ => ?_
  change (listCode (List.ofFn fun t => finiteSymbolCode ((w t).val i))).length ≤ _
  calc
    (listCode (List.ofFn fun t => finiteSymbolCode ((w t).val i))).length ≤
        (List.ofFn fun t => finiteSymbolCode ((w t).val i)).length *
          (2 * Fintype.card (Y i) + 1) := hcode _ _ (by
            intro x hx
            simp only [List.mem_ofFn] at hx
            obtain ⟨t, rfl⟩ := hx
            let q := (Fintype.equivFin (Y i) ((w t).val i)).val
            have hsize : Nat.size q ≤ q := Nat.size_le.mpr Nat.lt_two_pow_self
            have hbits : (Nat.bits q).length ≤ q + 1 := by
              rw [Nat.size_eq_bits_len]
              omega
            have hq : q < Fintype.card (Y i) :=
              ((Fintype.equivFin (Y i)) ((w t).val i)).isLt
            change (Nat.bits q).length ≤ Fintype.card (Y i)
            exact hbits.trans (Nat.add_one_le_iff.mpr hq))
    _ = N * (2 * Fintype.card (Y i) + 1) := by simp
    _ ≤ N * a := Nat.mul_le_mul_left N
      (Finset.le_sup (f := fun i : Fin n => 2 * Fintype.card (Y i) + 1)
        (Finset.mem_univ i))
    _ ≤ a * N + a := by
      rw [Nat.mul_comm N a]
      exact Nat.le_add_right _ _

private lemma exists_section_power_high_complexity (D : Map)
    (hD : isOptimalConditional D) (J₀ I₀ : Finset (Fin n))
    (hdisj₀ : Disjoint J₀ I₀) {Y : Fin n → Type}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (A : Finset (∀ i, Y i)) (hA : A.Nonempty) :
    ∃ c : ℕ, ∀ N : ℕ, ∃ w : Fin N → {a // a ∈ A},
      (N : ℝ) * Real.logb 2 (maxSection A J₀ I₀) ≤
        ((tupleCondK D (sectionPowerRows A w) J₀ I₀).toNat : ℝ) +
          (logSlack c N : ℝ) := by
  classical
  have _ := hdisj₀
  have hmax : 1 ≤ maxSection A J₀ I₀ := by
    obtain ⟨a, ha⟩ := hA
    have hmem : restrictTo J₀ a ∈ sectionOver A J₀ I₀ (restrictTo I₀ a) :=
      Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩, rfl⟩
    exact (Finset.card_pos.2 ⟨_, hmem⟩).trans_le
      (Finset.le_sup (f := fun p => (sectionOver A J₀ I₀ p).card)
        (Finset.mem_univ _))
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset ((i : I₀) → Y i.val))
    ⟨restrictTo I₀ hA.choose, Finset.mem_univ _⟩
    (fun p => (sectionOver A J₀ I₀ p).card)
  let S := sectionOver A J₀ I₀ p
  have hcardS : S.card = maxSection A J₀ I₀ := by
    simpa [S, maxSection] using hp.symm
  have hS : S.Nonempty := Finset.card_pos.1 (lt_of_lt_of_le (by omega) (hcardS ▸ hmax))
  have hwitness : ∀ s : {s // s ∈ S},
      ∃ a ∈ A.filter fun a => restrictTo I₀ a = p, restrictTo J₀ a = s.1 := by
    intro s
    apply Finset.mem_image.mp
    simpa only [S, sectionOver] using s.property
  let lift : {s // s ∈ S} → (∀ i, Y i) := fun s => (hwitness s).choose
  have hlift (s : {s // s ∈ S}) :
      lift s ∈ A.filter (fun a => restrictTo I₀ a = p) ∧
        restrictTo J₀ (lift s) = s.1 := by
    exact (hwitness s).choose_spec
  have hsymbol (i : Fin n) :
      Function.Injective (@finiteSymbolCode (Y i) (inferInstance)) := by
    intro x y hxy
    apply (Fintype.equivFin (Y i)).injective
    apply Fin.ext
    exact natBits_injective hxy
  refine ⟨1, fun N => ?_⟩
  let word : (Fin N → {s // s ∈ S}) → Fin N → {a // a ∈ A} := fun v t =>
    ⟨lift (v t), (Finset.mem_filter.1 (hlift (v t)).1).1⟩
  have hSpos : 0 < S.card := Finset.card_pos.2 hS
  obtain ⟨s₀, hs₀⟩ := hS
  let v₀ : Fin N → {s // s ∈ S} := fun _ => ⟨s₀, hs₀⟩
  let y := subtupleCode (sectionPowerRows A (word v₀)) I₀
  let f : (Fin N → {s // s ∈ S}) → BitString := fun v =>
    subtupleCode (sectionPowerRows A (word v)) J₀
  have hcond : ∀ v, subtupleCode (sectionPowerRows A (word v)) I₀ = y := by
    intro v
    unfold y subtupleCode
    apply congrArg listCode
    apply List.map_congr_left
    intro i hi
    unfold sectionPowerRows
    apply congrArg listCode
    apply congrArg List.ofFn
    funext t
    apply congrArg finiteSymbolCode
    have hv := (Finset.mem_filter.1 (hlift (v t)).1).2
    have hv₀ := (Finset.mem_filter.1 (hlift (v₀ t)).1).2
    exact congrFun (hv.trans hv₀.symm) ⟨i, (Finset.mem_sort _).1 hi⟩
  have hf : Function.Injective f := by
    intro v u hvu
    funext t
    apply Subtype.ext
    have hout := listCode_injective hvu
    have hrestrict : restrictTo J₀ (lift (v t)) = restrictTo J₀ (lift (u t)) := by
      funext j
      have hrow := List.map_inj_left.mp hout j.1 ((Finset.mem_sort _).2 j.2)
      have htimes := listCode_injective hrow
      have hcode := congrFun (List.ofFn_injective htimes) t
      exact hsymbol j.1 hcode
    exact (hlift (v t)).2.symm.trans (hrestrict.trans (hlift (u t)).2)
  let q := Nat.log 2 (S.card ^ N)
  have hex : ∃ v : Fin N → {s // s ∈ S},
      q ≤ (condK D (f v) y).toNat := by
    by_cases hq : q = 0
    · exact ⟨v₀, hq ▸ Nat.zero_le _⟩
    · by_contra hnone
      have h : ∀ v : Fin N → {s // s ∈ S},
          (condK D (f v) y).toNat < q := by
        intro v
        exact Nat.lt_of_not_ge (fun hv => hnone ⟨v, hv⟩)
      let C := compressibleWords D y (q - 1)
      have hmaps : Set.MapsTo f (Finset.univ : Finset (Fin N → {s // s ∈ S})) C := by
        intro v _
        have hfinite : condK D (f v) y ≠ ⊤ := by
          rw [← hcond v]
          exact tupleCondK_ne_top D hD (sectionPowerRows A (word v)) J₀ I₀
        have hvlt := h v
        have hnat : (condK D (f v) y).toNat ≤ q - 1 := by omega
        have hle : condK D (f v) y ≤ ((q - 1 : ℕ) : ℕ∞) := by
          rw [← ENat.natCast_toNat hfinite]
          exact_mod_cast hnat
        change f v ∈ compressibleWords D y (q - 1)
        rw [compressibleWords, Finset.mem_filter]
        refine ⟨?_, hle⟩
        obtain ⟨r, hr, hrlen⟩ := exists_program_of_KP_ne_top
          (M := D) (x := f v) (y := y) (by rwa [KP_eq_condK])
        rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
        refine ⟨r, mem_programsLe (q - 1) r ?_, progToOut_eq_some.mpr hr⟩
        have hrlenNat : r.length = (condK D (f v) y).toNat := by
          have hrlen' := congrArg ENat.toNat hrlen
          simpa [KP_eq_condK] using hrlen'
        rw [hrlenNat]
        exact hnat
      have hcount := Finset.card_le_card_of_injOn f hmaps hf.injOn
      have hcompress := card_compressibleWordsLt D y (q - 1)
      have hpow : 2 ^ q ≤ S.card ^ N :=
        Nat.pow_log_le_self 2 (by
          exact pow_ne_zero N hSpos.ne')
      have hdomain :
          (Finset.univ : Finset (Fin N → {s // s ∈ S})).card = S.card ^ N := by
        simp
      rw [hdomain] at hcount
      change C.card < 2 ^ (q - 1 + 1) at hcompress
      have hsucc : q - 1 + 1 = q := by omega
      rw [hsucc] at hcompress
      omega
  obtain ⟨v, hv⟩ := hex
  refine ⟨word v, ?_⟩
  have hpowpos : 0 < S.card ^ N := pow_pos hSpos N
  have hpowlt : S.card ^ N < 2 ^ (q + 1) := by
    exact Nat.lt_pow_succ_log_self (by omega) _
  have hlog : Real.logb 2 (S.card ^ N) ≤ (q : ℝ) + 1 := by
    have hmono : Real.logb 2 (S.card ^ N) ≤ Real.logb 2 (2 ^ (q + 1) : ℕ) := by
      apply (Real.logb_le_logb (by norm_num) (by exact_mod_cast hpowpos)
        (by positivity)).2
      exact_mod_cast hpowlt.le
    simpa [Real.logb_pow, Real.logb_self_eq_one] using hmono
  calc
    (N : ℝ) * Real.logb 2 (maxSection A J₀ I₀) =
        Real.logb 2 (S.card ^ N) := by
      rw [← hcardS, Real.logb_pow]
    _ ≤ (q : ℝ) + 1 := hlog
    _ ≤ ((tupleCondK D (sectionPowerRows A (word v)) J₀ I₀).toNat : ℝ) +
        (logSlack 1 N : ℝ) := by
      rw [tupleCondK, hcond v]
      have hslack : 1 ≤ logSlack 1 N := by simp [logSlack]
      exact_mod_cast Nat.add_le_add hv hslack

/- A partial recursive reconstruction of `x` from a plain description of `z` and the
condition `y` turns the plain complexity of `z` into an upper bound for `C(x | y)`. -/
private lemma condK_le_plainK_of_partrec_reconstruction (D : Map)
    (hD : isOptimalConditional D) (F : BitString → BitString →. BitString)
    (hF : Partrec fun p : BitString × BitString => F p.1 p.2) :
    ∃ c : ℕ, ∀ z y x, x ∈ F z y → condK D x y ≤ plainK D z + (c : ℕ∞) := by
  let E : Map := fun p => (D (p.1, [])).bind fun z => F z p.2
  have hE : isDecompressor E :=
    (hD.1.comp (Computable.fst.pair (Computable.const []))).bind
      (hF.comp (Computable.snd.pair (Computable.snd.comp Computable.fst))).to₂
  obtain ⟨c, hc⟩ := hD.2 E hE
  refine ⟨c, fun z y x hx => (hc x y).trans ?_⟩
  gcongr
  apply sInf_le_sInf
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨p, Part.mem_bind hp hx, rfl⟩

/- Turn a word of indices into the row-major code obtained from a fixed table of columns. -/
private def indexedPowerRowsCode (T : List (List BitString)) (k : ℕ)
    (u : List ℕ) : BitString :=
  listCode ((List.range k).map fun i =>
    listCode (u.map fun q => (T.getD q []).getD i []))

private lemma indexedPowerRowsCode_primrec (T : List (List BitString)) (k : ℕ) :
    Primrec (indexedPowerRowsCode T k) := by
  unfold indexedPowerRowsCode
  have hentry : Primrec fun p : (List ℕ × ℕ) × ℕ =>
      (T.getD p.2 []).getD p.1.2 [] :=
    (Primrec.list_getD []).comp
      ((Primrec.list_getD []).comp (Primrec.const T) Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  have hrow : Primrec₂ fun (u : List ℕ) (i : ℕ) =>
      listCode (u.map fun q => (T.getD q []).getD i []) :=
    (listCode_primrec.comp (Primrec.list_map Primrec.fst hentry.to₂)).to₂
  refine listCode_primrec.comp (Primrec.list_map (Primrec.const _) ?_)
  exact hrow

private def decodedNatList (q : ℕ) : List ℕ :=
  (Encodable.decode (α := List ℕ) q).getD []

private lemma decodedNatList_primrec : Primrec decodedNatList := by
  exact Primrec.option_getD.comp Primrec.decode (Primrec.const [])

private def sectionReconstructionGood (R : List ℕ) (TI : List (List BitString))
    (kI : ℕ) (dec : BitString → List ℕ) (z y : BitString) (q : ℕ) : Bool :=
  let u := decodedNatList q
  (u.all fun a => decide (a < R.length)) &&
    decide (u.map (R.getD · 0) = dec z) &&
      decide (indexedPowerRowsCode TI kI u = y)

private def sectionReconstruction (R : List ℕ) (TI TJ : List (List BitString))
    (kI kJ : ℕ) (dec : BitString → List ℕ) (z y : BitString) : Part BitString :=
  (Nat.rfind fun q => Part.some (sectionReconstructionGood R TI kI dec z y q)).bind
    fun q => Part.some (indexedPowerRowsCode TJ kJ (decodedNatList q))

private lemma sectionReconstruction_partrec (R : List ℕ)
    (TI TJ : List (List BitString)) (kI kJ : ℕ) (dec : BitString → List ℕ)
    (hdec : Primrec dec) :
    Partrec fun p : BitString × BitString =>
      sectionReconstruction R TI TJ kI kJ dec p.1 p.2 := by
  have hu : Primrec fun p : (BitString × BitString) × ℕ => decodedNatList p.2 :=
    decodedNatList_primrec.comp Primrec.snd
  have hvalid : Primrec fun p : (BitString × BitString) × ℕ =>
      (decodedNatList p.2).all fun a => decide (a < R.length) := by
    refine (Primrec.list_all ?_).comp hu
    exact (PrimrecPred.decide (Primrec.nat_lt.comp Primrec.id
      (Primrec.const R.length)))
  have hranks : Primrec fun p : (BitString × BitString) × ℕ =>
      (decodedNatList p.2).map (R.getD · 0) := by
    exact Primrec.list_map hu
      ((Primrec.list_getD 0).comp (Primrec.const R) Primrec.snd).to₂
  have hdec' : Primrec fun p : (BitString × BitString) × ℕ => dec p.1.1 :=
    hdec.comp (Primrec.fst.comp Primrec.fst)
  have hrankEq : Primrec fun p : (BitString × BitString) × ℕ =>
      decide ((decodedNatList p.2).map (R.getD · 0) = dec p.1.1) :=
    PrimrecPred.decide (Primrec.eq.comp hranks hdec')
  have hcode : Primrec fun p : (BitString × BitString) × ℕ =>
      indexedPowerRowsCode TI kI (decodedNatList p.2) :=
    (indexedPowerRowsCode_primrec TI kI).comp hu
  have hy : Primrec fun p : (BitString × BitString) × ℕ => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hcodeEq : Primrec fun p : (BitString × BitString) × ℕ =>
      decide (indexedPowerRowsCode TI kI (decodedNatList p.2) = p.1.2) :=
    PrimrecPred.decide (Primrec.eq.comp hcode hy)
  have hgood : Computable₂ (fun p : BitString × BitString => fun q =>
      sectionReconstructionGood R TI kI dec p.1 p.2 q) := by
    exact (Primrec.and.comp (Primrec.and.comp hvalid hrankEq) hcodeEq).to_comp.to₂
  have hout : Computable₂ (fun _p : BitString × BitString => fun q =>
      indexedPowerRowsCode TJ kJ (decodedNatList q)) := by
    exact ((indexedPowerRowsCode_primrec TJ kJ).comp
      (decodedNatList_primrec.comp Primrec.snd)).to_comp.to₂
  exact Partrec.bind (Partrec.rfind hgood.partrec₂) hout.partrec₂

/- The `J`-coordinates of a point, encoded as a list of symbol codes. -/
private noncomputable def sectionKey {Y : Fin n → Type} [∀ i, Fintype (Y i)]
    (J : Finset (Fin n)) (p : (j : J) → Y j.val) : List BitString :=
  List.ofFn fun q => finiteSymbolCode (p ((Fintype.equivFin J).symm q))

private lemma sectionKey_injective {Y : Fin n → Type} [∀ i, Fintype (Y i)]
    (J : Finset (Fin n)) : Function.Injective (sectionKey (Y := Y) J) := by
  intro p p' hk
  funext j
  have hh := finiteSymbolCode_injective
    (congrFun (List.ofFn_injective hk) (Fintype.equivFin J j))
  rwa [Equiv.symm_apply_apply] at hh

/- The rank of a point inside its `J`-section over its `I`-coordinates: the position of its
encoded `J`-coordinates in the encoded section. -/
private noncomputable def sectionRank {Y : Fin n → Type} [∀ i, Fintype (Y i)]
    [∀ i, DecidableEq (Y i)] (A : Finset (∀ i, Y i)) (J I : Finset (Fin n))
    (a : ∀ i, Y i) : ℕ :=
  (((sectionOver A J I (restrictTo I a)).image (sectionKey J)).toList.findIdx
    fun z => decide (z = sectionKey J (restrictTo J a)))

private lemma sectionRank_lt_card {Y : Fin n → Type} [∀ i, Fintype (Y i)]
    [∀ i, DecidableEq (Y i)] {A : Finset (∀ i, Y i)} (J I : Finset (Fin n)) {a : ∀ i, Y i}
    (ha : a ∈ A) :
    sectionRank A J I a < ((sectionOver A J I (restrictTo I a)).image (sectionKey J)).card := by
  have hm : sectionKey J (restrictTo J a) ∈
      ((sectionOver A J I (restrictTo I a)).image (sectionKey J)).toList :=
    Finset.mem_toList.2 (Finset.mem_image.2
      ⟨restrictTo J a, Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩, rfl⟩, rfl⟩)
  rw [sectionRank, ← Finset.length_toList]
  exact List.findIdx_lt_length_of_exists
    (p := fun z => decide (z = sectionKey J (restrictTo J a))) ⟨_, hm, by simp⟩

/- A section has at most `m_A(J | I)` points, so the rank of a point of `A` is below it. -/
private lemma sectionRank_lt_maxSection {Y : Fin n → Type} [∀ i, Fintype (Y i)]
    [∀ i, DecidableEq (Y i)] {A : Finset (∀ i, Y i)} (J I : Finset (Fin n)) {a : ∀ i, Y i}
    (ha : a ∈ A) : sectionRank A J I a < maxSection A J I :=
  (sectionRank_lt_card J I ha).trans_le (Finset.card_image_le.trans
    (Finset.le_sup (f := fun p => (sectionOver A J I p).card)
      (Finset.mem_univ (restrictTo I a))))

private lemma getD_sectionRank {Y : Fin n → Type} [∀ i, Fintype (Y i)]
    [∀ i, DecidableEq (Y i)] {A : Finset (∀ i, Y i)} (J I : Finset (Fin n)) {a : ∀ i, Y i}
    (ha : a ∈ A) :
    ((sectionOver A J I (restrictTo I a)).image (sectionKey J)).toList.getD
      (sectionRank A J I a) [] = sectionKey J (restrictTo J a) := by
  have hlt := sectionRank_lt_card J I ha
  rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
  have hget := List.findIdx_getElem (p := fun z => decide (z = sectionKey J (restrictTo J a)))
    (xs := ((sectionOver A J I (restrictTo I a)).image (sectionKey J)).toList)
    (w := by simpa [sectionRank] using hlt)
  simpa [sectionRank] using of_decide_eq_true hget

/- The `I`-coordinates and the rank inside the section determine the `J`-coordinates. -/
private lemma restrictTo_eq_of_sectionRank_eq {Y : Fin n → Type} [∀ i, Fintype (Y i)]
    [∀ i, DecidableEq (Y i)] {A : Finset (∀ i, Y i)} (J I : Finset (Fin n))
    {a b : ∀ i, Y i} (ha : a ∈ A) (hb : b ∈ A) (hI : restrictTo I a = restrictTo I b)
    (hr : sectionRank A J I a = sectionRank A J I b) :
    restrictTo J a = restrictTo J b := by
  apply sectionKey_injective J
  rw [← getD_sectionRank J I ha, ← getD_sectionRank J I hb, hI, hr]

/- Indexing a table of the `S`-keys of the points of `A` by the word `w` reproduces the code of
the `S`-rows of the power of `A` along `w`. -/
private lemma indexedPowerRowsCode_ofFn_eq {Y : Fin n → Type} [∀ i, Fintype (Y i)]
    [∀ i, DecidableEq (Y i)] {A : Finset (∀ i, Y i)} (S : Finset (Fin n))
    (e : {a // a ∈ A} ≃ Fin (Fintype.card {a // a ∈ A})) {N : ℕ}
    (w : Fin N → {a // a ∈ A}) :
    indexedPowerRowsCode
        (List.ofFn fun q => (S.sort (· ≤ ·)).map fun i => finiteSymbolCode ((e.symm q).val i))
        (S.sort (· ≤ ·)).length (List.ofFn fun t => (e (w t)).val) =
      subtupleCode (sectionPowerRows A w) S := by
  unfold indexedPowerRowsCode subtupleCode
  congr 1
  apply List.ext_getElem (by simp)
  intro r hr hr'
  simp only [List.getElem_map, List.getElem_range]
  congr 1
  apply List.ext_getElem (by simp)
  intro t ht ht'
  simp only [List.getElem_map, List.getElem_ofFn]
  let tt : Fin N := ⟨t, by simpa using ht'⟩
  have htable : (List.ofFn fun q : Fin (Fintype.card {a // a ∈ A}) =>
      (S.sort (· ≤ ·)).map fun i => finiteSymbolCode ((e.symm q).val i)).getD
        (e (w tt)).val [] = (S.sort (· ≤ ·)).map fun i => finiteSymbolCode ((w tt).val i) := by
    rw [List.getD_eq_getElem _ _ (by simpa using (e (w tt)).isLt)]
    simp
  rw [htable]
  rw [List.getD_eq_getElem _ _ (by simpa using hr')]
  rw [List.getElem_map]

/- Equal row-major codes of two index words give equal columns, position by position. -/
private lemma indexedPowerRowsCode_column_eq {T : List (List BitString)} {k : ℕ}
    {v v' : List ℕ} (hvlen : v.length = v'.length) (hv : ∀ q ∈ v, q < T.length)
    (hv' : ∀ q ∈ v', q < T.length) (hlen : ∀ q, q < T.length → (T.getD q []).length = k)
    (heq : indexedPowerRowsCode T k v = indexedPowerRowsCode T k v') {t : ℕ}
    (ht : t < v.length) : T.getD (v.getD t 0) [] = T.getD (v'.getD t 0) [] := by
  have ht' : t < v'.length := by omega
  have hq : v.getD t 0 ∈ v := by
    rw [List.getD_eq_getElem _ _ ht]
    exact List.getElem_mem ht
  have hq' : v'.getD t 0 ∈ v' := by
    rw [List.getD_eq_getElem _ _ ht']
    exact List.getElem_mem ht'
  apply List.ext_getElem (by rw [hlen _ (hv _ hq), hlen _ (hv' _ hq')])
  intro r hr hr'
  have houter := listCode_injective heq
  have hrowCode := congrArg (fun L => L.getD r []) houter
  have hrk : r < k := by
    rw [hlen _ (hv _ hq)] at hr
    exact hr
  have hseq : v.map (fun q => (T.getD q []).getD r []) =
      v'.map (fun q => (T.getD q []).getD r []) := by
    apply listCode_injective
    simpa [List.getD_map, hrk] using hrowCode
  have htseq := congrArg (fun L => L.getD t []) hseq
  change (v.map (fun q => (T.getD q []).getD r [])).getD t [] =
    (v'.map (fun q => (T.getD q []).getD r [])).getD t [] at htseq
  rw [List.getD_eq_getElem _ _ (by simpa using ht),
    List.getD_eq_getElem _ _ (by simpa using ht')] at htseq
  simp only [List.getElem_map] at htseq
  rw [← List.getD_eq_getElem _ _ hr, ← List.getD_eq_getElem _ _ hr']
  simpa [List.getD_eq_getElem, ht, ht'] using htseq

/- The empirical distribution of a word over an alphabet of `M` letters has entropy at most
`log M`. -/
private lemma entropyDist_freq_le_logb {M N : ℕ} (hM : 0 < M) (r : Fin N → Fin M) :
    entropyDist (fun a => (freq r a : ℝ) / N) ≤ Real.logb 2 M := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hlog : 0 ≤ Real.logb 2 (M : ℝ) :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast hM)
    simpa [entropyDist] using hlog
  · simpa using (entropyDist_le_logb_card
      (p := fun a => (freq r a : ℝ) / N) (fun a => by positivity) (by
        rw [← Finset.sum_div, ← Nat.cast_sum, sum_freq]
        simp [hN.ne']))

/- Over a table of the points of a finite type `B`, an index word is determined letter by letter
by its `iKey`-column and its rank word whenever `iKey` and the rank determine `jKey`: equal
`iKey`-rows and equal rank words give equal `jKey`-rows. -/
private lemma indexedPowerRowsCode_jKey_eq {B : Type} [Fintype B] {M kI kJ : ℕ}
    (e : B ≃ Fin (Fintype.card B)) {iKey jKey : B → List BitString} {rank : B → Fin M}
    (hilen : ∀ b, (iKey b).length = kI)
    (hrank : ∀ {a b : B}, iKey a = iKey b → rank a = rank b → jKey a = jKey b)
    {u0 u : List ℕ} (hu0 : ∀ q ∈ u0, q < Fintype.card B) (hu : ∀ q ∈ u, q < Fintype.card B)
    (hR : u0.map ((List.ofFn fun q => alphabetIndex (Fin M) (rank (e.symm q))).getD · 0) =
      u.map ((List.ofFn fun q => alphabetIndex (Fin M) (rank (e.symm q))).getD · 0))
    (hI : indexedPowerRowsCode (List.ofFn fun q => iKey (e.symm q)) kI u0 =
      indexedPowerRowsCode (List.ofFn fun q => iKey (e.symm q)) kI u) :
    indexedPowerRowsCode (List.ofFn fun q => jKey (e.symm q)) kJ u0 =
      indexedPowerRowsCode (List.ofFn fun q => jKey (e.symm q)) kJ u := by
  set TI : List (List BitString) := List.ofFn fun q => iKey (e.symm q) with hTI
  set TJ : List (List BitString) := List.ofFn fun q => jKey (e.symm q) with hTJ
  set R : List ℕ := List.ofFn fun q => alphabetIndex (Fin M) (rank (e.symm q)) with hRdef
  have hu0len : u0.length = u.length := by
    rw [← List.length_map (f := fun q => R.getD q 0), hR, List.length_map]
  have hTIlen : ∀ q, q < TI.length → (TI.getD q []).length = kI := by
    intro q hq
    rw [List.getD_eq_getElem _ _ hq]
    simp [TI, hilen]
  have hicol := fun t (ht : t < u0.length) => indexedPowerRowsCode_column_eq hu0len
    (fun q hq => by simpa [TI] using hu0 q hq) (fun q hq => by simpa [TI] using hu q hq)
    hTIlen hI ht
  have hTIget (q : ℕ) (hq : q < Fintype.card B) :
      TI.getD q [] = iKey (e.symm ⟨q, hq⟩) := by
    rw [List.getD_eq_getElem _ _ (by simpa [TI] using hq)]
    simp [TI]
  have hRget (q : ℕ) (hq : q < Fintype.card B) :
      R.getD q 0 = alphabetIndex (Fin M) (rank (e.symm ⟨q, hq⟩)) := by
    rw [List.getD_eq_getElem _ _ (by simpa [R] using hq)]
    simp [R]
  have hTJget (q : ℕ) (hq : q < Fintype.card B) :
      TJ.getD q [] = jKey (e.symm ⟨q, hq⟩) := by
    rw [List.getD_eq_getElem _ _ (by simpa [TJ] using hq)]
    simp [TJ]
  have hjcols : u0.map (TJ.getD · []) = u.map (TJ.getD · []) := by
    apply List.ext_getElem (by simp [hu0len])
    intro t ht ht'
    have ht0 : t < u0.length := by simpa using ht
    have htu : t < u.length := by omega
    simp only [List.getElem_map]
    have q0mem : u0.getD t 0 ∈ u0 := by
      rw [List.getD_eq_getElem _ _ ht0]
      exact List.getElem_mem ht0
    have qumem : u.getD t 0 ∈ u := by
      rw [List.getD_eq_getElem _ _ htu]
      exact List.getElem_mem htu
    have q0card := hu0 _ q0mem
    have qucard := hu _ qumem
    let b0 : B := e.symm ⟨u0.getD t 0, q0card⟩
    let b : B := e.symm ⟨u.getD t 0, qucard⟩
    have hi : iKey b0 = iKey b := by
      rw [← hTIget _ q0card, ← hTIget _ qucard]
      exact hicol t ht0
    have hri : rank b0 = rank b := by
      apply alphabetIndex_injective
      have hh := congrArg (fun L => L.getD t 0) hR
      change (u0.map (R.getD · 0)).getD t 0 =
        (u.map (R.getD · 0)).getD t 0 at hh
      rw [List.getD_eq_getElem _ _ (by simpa using ht0),
        List.getD_eq_getElem _ _ (by simpa using htu)] at hh
      simp only [List.getElem_map] at hh
      rw [← List.getD_eq_getElem _ _ ht0, ← List.getD_eq_getElem _ _ htu] at hh
      rw [hRget _ q0card, hRget _ qucard] at hh
      simpa [b0, b] using hh
    have hj := hrank hi hri
    rw [← List.getD_eq_getElem _ _ ht0, ← List.getD_eq_getElem _ _ htu]
    rw [hTJget _ q0card, hTJget _ qucard]
    simpa [b0, b] using hj
  unfold indexedPowerRowsCode
  congr 1
  apply List.map_congr_left
  intro r hr
  congr 1
  simpa [List.map_map, Function.comp_def] using
    congrArg (List.map fun z => z.getD r []) hjcols

/- The reconstruction search halts at the first good index word.  When every good index word
has the same `TJ`-rows as `u`, the search outputs those rows. -/
private lemma mem_sectionReconstruction {R : List ℕ} {TI TJ : List (List BitString)}
    {kI kJ : ℕ} {dec : BitString → List ℕ} {z y : BitString} {u : List ℕ}
    (hgood : sectionReconstructionGood R TI kI dec z y (Encodable.encode u) = true)
    (hdet : ∀ q, sectionReconstructionGood R TI kI dec z y q = true →
      indexedPowerRowsCode TJ kJ (decodedNatList q) = indexedPowerRowsCode TJ kJ u) :
    indexedPowerRowsCode TJ kJ u ∈ sectionReconstruction R TI TJ kI kJ dec z y := by
  classical
  have hex : ∃ q, sectionReconstructionGood R TI kI dec z y q = true := ⟨_, hgood⟩
  unfold sectionReconstruction
  rw [Part.mem_bind_iff]
  refine ⟨Nat.find hex, ?_, ?_⟩
  · refine Nat.mem_rfind.2 ⟨by simpa using Nat.find_spec hex, fun hq => ?_⟩
    simp [Nat.find_min hex hq]
  · simp [hdet _ (Nat.find_spec hex)]

private lemma exists_section_power_condK_upper_bound (D : Map)
    (hD : isOptimalConditional D) (J I : Finset (Fin n)) (hdisj : Disjoint J I)
    {Y : Fin n → Type} [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (A : Finset (∀ i, Y i)) :
    ∃ c : ℕ, ∀ (N : ℕ) (w : Fin N → {a // a ∈ A}),
      ((tupleCondK D (sectionPowerRows A w) J I).toNat : ℝ) ≤
        (N : ℝ) * Real.logb 2 (maxSection A J I) + (logSlack c N : ℝ) := by
  classical
  have _ := hdisj
  rcases A.eq_empty_or_nonempty with rfl | hA
  · let c := (tupleCondK D (fun _ : Fin n => ([] : BitString)) J I).toNat
    refine ⟨c, fun N w => ?_⟩
    have hN : N = 0 := by
      by_contra h
      exact Finset.notMem_empty _ (w ⟨0, Nat.pos_of_ne_zero h⟩).property
    subst N
    have hw : sectionPowerRows ∅ w = fun _ : Fin n => ([] : BitString) := by
      funext i
      simp [sectionPowerRows]
    rw [hw]
    simp [c, logSlack]
  · let B := {a // a ∈ A}
    let e := Fintype.equivFin B
    let sI := I.sort (· ≤ ·)
    let sJ := J.sort (· ≤ ·)
    let iKey : B → List BitString := fun a => sI.map fun i => finiteSymbolCode (a.val i)
    let jKey : B → List BitString := fun a => sJ.map fun i => finiteSymbolCode (a.val i)
    have hiKey : ∀ {a b : B}, iKey a = iKey b →
        restrictTo I a.val = restrictTo I b.val := by
      intro a b hab
      funext i
      have hh := List.map_inj_left.1 hab i.val ((Finset.mem_sort _).2 i.2)
      exact finiteSymbolCode_injective hh
    let M := maxSection A J I
    have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le _)
      (sectionRank_lt_maxSection J I hA.choose_spec)
    let rank (a : B) : Fin M := ⟨sectionRank A J I a.val, sectionRank_lt_maxSection J I a.property⟩
    have hrank : ∀ {a b : B}, iKey a = iKey b → rank a = rank b →
        jKey a = jKey b := by
      intro a b hi hr
      have hj := restrictTo_eq_of_sectionRank_eq J I a.property b.property (hiKey hi)
        (congrArg Fin.val hr)
      apply List.map_congr_left
      intro j hjJ
      exact congrArg finiteSymbolCode (congrFun hj ⟨j, (Finset.mem_sort _).1 hjJ⟩)
    let TI : List (List BitString) := List.ofFn fun q : Fin (Fintype.card B) => iKey (e.symm q)
    let TJ : List (List BitString) := List.ofFn fun q : Fin (Fintype.card B) => jKey (e.symm q)
    let R : List ℕ := List.ofFn fun q : Fin (Fintype.card B) =>
      alphabetIndex (Fin M) (rank (e.symm q))
    obtain ⟨dec, hdec, hdecw⟩ := exists_primrec_wordBits_decoder (Fin M)
    let F := sectionReconstruction R TI TJ sI.length sJ.length dec
    have hF : Partrec fun p : BitString × BitString => F p.1 p.2 :=
      sectionReconstruction_partrec R TI TJ sI.length sJ.length dec hdec
    obtain ⟨cRec, hRec⟩ := condK_le_plainK_of_partrec_reconstruction D hD F hF
    obtain ⟨cWord, hWord⟩ := exists_plainK_word_le_entropy_freq (Fin M) D hD
    obtain ⟨cPlain, hPlain⟩ := plainK_le_length D hD
    refine ⟨cWord + cRec, fun N w => ?_⟩
    let rwrd : Fin N → Fin M := fun t => rank (w t)
    let u : List ℕ := List.ofFn fun t => (e (w t)).val
    have huvalid : ∀ q ∈ u, q < R.length := by
      intro q hq
      simp only [u, List.mem_ofFn] at hq
      obtain ⟨t, rfl⟩ := hq
      simp [R]
    have hTI : indexedPowerRowsCode TI sI.length u =
        subtupleCode (sectionPowerRows A w) I :=
      indexedPowerRowsCode_ofFn_eq I e w
    have hTJ : indexedPowerRowsCode TJ sJ.length u =
        subtupleCode (sectionPowerRows A w) J :=
      indexedPowerRowsCode_ofFn_eq J e w
    have hRu : u.map (R.getD · 0) = dec (finWordBits (Fin M) rwrd) := by
      unfold finWordBits
      rw [hdecw]
      apply List.ext_getElem (by simp [u])
      intro t ht ht'
      simp only [u, List.getElem_map, List.getElem_ofFn, rwrd]
      have heLt : (e (w ⟨t, by simpa [u] using ht'⟩)).val < Fintype.card B :=
        (e (w ⟨t, by simpa [u] using ht'⟩)).isLt
      rw [List.getD_eq_getElem _ _ (by simp [R])]
      simp [R]
    have hdecode : decodedNatList (Encodable.encode u) = u := by
      simp [decodedNatList]
    have hgood : sectionReconstructionGood R TI sI.length dec
        (finWordBits (Fin M) rwrd) (subtupleCode (sectionPowerRows A w) I)
          (Encodable.encode u) = true := by
      simp only [sectionReconstructionGood, hdecode, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨List.all_eq_true.2 ?_, hRu⟩, hTI⟩
      intro q hq
      exact decide_eq_true (huvalid q hq)
    have hmem : subtupleCode (sectionPowerRows A w) J ∈
        F (finWordBits (Fin M) rwrd) (subtupleCode (sectionPowerRows A w) I) := by
      rw [← hTJ]
      refine mem_sectionReconstruction hgood fun q hq => ?_
      simp only [sectionReconstructionGood, Bool.and_eq_true, decide_eq_true_eq] at hq
      exact indexedPowerRowsCode_jKey_eq (kI := sI.length) (kJ := sJ.length) e
        (iKey := iKey) (jKey := jKey) (rank := rank) (fun b => by simp [iKey]) hrank
        (fun q' hq' => by simpa [R] using of_decide_eq_true (List.all_eq_true.1 hq.1.1 q' hq'))
        (fun q' hq' => by simpa [R] using huvalid q' hq')
        (by rw [hq.1.2, hRu]) (by rw [hq.2, hTI])
    have hcomp := hRec (finWordBits (Fin M) rwrd)
      (subtupleCode (sectionPowerRows A w) I)
      (subtupleCode (sectionPowerRows A w) J) hmem
    have hfin : plainK D (finWordBits (Fin M) rwrd) ≠ ⊤ :=
      ne_top_of_le_natCast_add (hPlain _)
    rw [← ENat.natCast_toNat hfin] at hcomp
    have hnat := ENat.toNat_le_of_le_natCast hcomp
    have hcompR : ((tupleCondK D (sectionPowerRows A w) J I).toNat : ℝ) ≤
        ((plainK D (finWordBits (Fin M) rwrd)).toNat : ℝ) + cRec := by
      exact_mod_cast hnat
    have hent : entropyDist (fun a => (freq rwrd a : ℝ) / N) ≤ Real.logb 2 M :=
      entropyDist_freq_le_logb hM rwrd
    have hwbd := hWord N rwrd
    have hslack : (logSlack cWord N : ℝ) + cRec ≤
        logSlack (cWord + cRec) N := by
      simp only [logSlack]
      push_cast
      have hb : (0 : ℝ) ≤ ((Nat.bits N).length : ℝ) := Nat.cast_nonneg _
      nlinarith
    calc
      ((tupleCondK D (sectionPowerRows A w) J I).toNat : ℝ) ≤
          ((plainK D (finWordBits (Fin M) rwrd)).toNat : ℝ) + cRec := hcompR
      _ ≤ (N : ℝ) * entropyDist (fun a => (freq rwrd a : ℝ) / N) +
          (logSlack cWord N : ℝ) + cRec := by linarith
      _ ≤ (N : ℝ) * Real.logb 2 M +
          ((logSlack cWord N : ℝ) + cRec) := by
            nlinarith [mul_le_mul_of_nonneg_left hent (Nat.cast_nonneg N)]
      _ ≤ (N : ℝ) * Real.logb 2 (maxSection A J I) +
          (logSlack (cWord + cRec) N : ℝ) := by
            simpa [M] using add_le_add_left hslack ((N : ℝ) * Real.logb 2 M)

private lemma section_power_positive_combination_complexity_upper_bound (D : Map)
    (hD : isOptimalConditional D) (m : ℕ) (J I : Fin m → Finset (Fin n))
    (mu : Fin m → ℝ) (hmu : ∀ k, 0 ≤ mu k)
    (hdisj : ∀ k, Disjoint (J k) (I k)) {Y : Fin n → Type}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (A : Finset (∀ i, Y i)) :
    ∃ c : ℕ, ∀ (N : ℕ) (w : Fin N → {a // a ∈ A}),
      (∑ k, mu k *
          ((tupleCondK D (sectionPowerRows A w) (J k) (I k)).toNat : ℝ)) ≤
        (N : ℝ) * (∑ k, mu k * Real.logb 2 (maxSection A (J k) (I k))) +
          (logSlack c N : ℝ) := by
  choose ck hck using fun k =>
    exists_section_power_condK_upper_bound D hD (J k) (I k) (hdisj k) A
  let s : ℝ := ∑ k, mu k * ck k
  let c : ℕ := ⌈s⌉₊
  refine ⟨c, fun N w => ?_⟩
  have hsc : s ≤ (c : ℝ) := by simpa [c] using Nat.le_ceil s
  have hterm : ∀ k, mu k *
      ((tupleCondK D (sectionPowerRows A w) (J k) (I k)).toNat : ℝ) ≤
      mu k * ((N : ℝ) * Real.logb 2 (maxSection A (J k) (I k)) +
        (logSlack (ck k) N : ℝ)) := fun k =>
    mul_le_mul_of_nonneg_left (hck k N w) (hmu k)
  have hslack : (∑ k, mu k * (logSlack (ck k) N : ℝ)) ≤
      (logSlack c N : ℝ) := by
    simp only [logSlack]
    push_cast
    calc
      ∑ k, mu k * (↑(ck k) * ↑(Nat.bits N).length + ↑(ck k)) =
          s * (↑(Nat.bits N).length + 1) := by
        simp only [mul_add, Finset.sum_add_distrib]
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul]
        simp [s]
      _ ≤ (c : ℝ) * (↑(Nat.bits N).length + 1) :=
        mul_le_mul_of_nonneg_right hsc (by positivity)
      _ = (c : ℝ) * ↑(Nat.bits N).length + c := by ring
  calc
    ∑ k, mu k *
        ((tupleCondK D (sectionPowerRows A w) (J k) (I k)).toNat : ℝ) ≤
        ∑ k, mu k * ((N : ℝ) * Real.logb 2 (maxSection A (J k) (I k)) +
          (logSlack (ck k) N : ℝ)) := Finset.sum_le_sum fun k _ => hterm k
    _ = (N : ℝ) * (∑ k, mu k * Real.logb 2 (maxSection A (J k) (I k))) +
        ∑ k, mu k * (logSlack (ck k) N : ℝ) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (N : ℝ) * (∑ k, mu k * Real.logb 2 (maxSection A (J k) (I k))) +
        (logSlack c N : ℝ) := by gcongr

private lemma exists_section_power_complexity_bounds (D : Map)
    (hD : isOptimalConditional D) (J₀ I₀ : Finset (Fin n))
    (hdisj₀ : Disjoint J₀ I₀) (m : ℕ) (J I : Fin m → Finset (Fin n))
    (mu : Fin m → ℝ) (hmu : ∀ k, 0 ≤ mu k)
    (hdisj : ∀ k, Disjoint (J k) (I k)) {Y : Fin n → Type}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (A : Finset (∀ i, Y i)) (hA : A.Nonempty) :
    ∃ a c : ℕ, ∀ N : ℕ, ∃ x : Fin n → BitString,
      tupleMaxLength x ≤ a * N + a ∧
        (N : ℝ) * Real.logb 2 (maxSection A J₀ I₀) ≤
          ((tupleCondK D x J₀ I₀).toNat : ℝ) + (logSlack c N : ℝ) ∧
        (∑ k, mu k * ((tupleCondK D x (J k) (I k)).toNat : ℝ)) ≤
          (N : ℝ) * (∑ k, mu k * Real.logb 2 (maxSection A (J k) (I k))) +
            (logSlack c N : ℝ) := by
  obtain ⟨a, hLength⟩ := exists_sectionPowerRows_length_bound A
  obtain ⟨cLower, hLower⟩ :=
    exists_section_power_high_complexity D hD J₀ I₀ hdisj₀ A hA
  obtain ⟨cUpper, hUpper⟩ :=
    section_power_positive_combination_complexity_upper_bound D hD m J I mu hmu hdisj A
  refine ⟨a, cLower + cUpper, fun N => ?_⟩
  obtain ⟨w, hwLower⟩ := hLower N
  refine ⟨sectionPowerRows A w, hLength N w, ?_, ?_⟩
  · calc
      (N : ℝ) * Real.logb 2 (maxSection A J₀ I₀) ≤
          ((tupleCondK D (sectionPowerRows A w) J₀ I₀).toNat : ℝ) +
            (logSlack cLower N : ℝ) := hwLower
      _ ≤ ((tupleCondK D (sectionPowerRows A w) J₀ I₀).toNat : ℝ) +
            (logSlack (cLower + cUpper) N : ℝ) := by
        rw [logSlack_add_constants]
        gcongr
        omega
  · calc
      (∑ k, mu k *
          ((tupleCondK D (sectionPowerRows A w) (J k) (I k)).toNat : ℝ)) ≤
          (N : ℝ) * (∑ k, mu k * Real.logb 2 (maxSection A (J k) (I k))) +
            (logSlack cUpper N : ℝ) := hUpper N w
      _ ≤ (N : ℝ) * (∑ k, mu k * Real.logb 2 (maxSection A (J k) (I k))) +
            (logSlack (cLower + cUpper) N : ℝ) := by
        rw [logSlack_add_constants]
        gcongr
        omega

private lemma exists_scaled_logb_maxSection_bound (D : Map)
    (hD : isOptimalConditional D) (J₀ I₀ : Finset (Fin n))
    (hdisj₀ : Disjoint J₀ I₀) (m : ℕ) (J I : Fin m → Finset (Fin n))
    (mu : Fin m → ℝ) (hmu : ∀ k, 0 ≤ mu k)
    (hdisj : ∀ k, Disjoint (J k) (I k))
    (hineq : ∃ c : ℕ, ∀ (N : ℕ) (x : Fin n → BitString), tupleMaxLength x ≤ N →
      ((tupleCondK D x J₀ I₀).toNat : ℝ) ≤
        (∑ k, mu k * ((tupleCondK D x (J k) (I k)).toNat : ℝ)) +
          (logSlack c N : ℝ))
    {Y : Fin n → Type} [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (A : Finset (∀ i, Y i)) (hA : A.Nonempty) :
    ∃ c : ℕ, ∀ N : ℕ,
      (N : ℝ) * Real.logb 2 (maxSection A J₀ I₀) ≤
        (N : ℝ) * (∑ k, mu k * Real.logb 2 (maxSection A (J k) (I k))) +
          (logSlack c N : ℝ) := by
  obtain ⟨a, cRows, hrows⟩ :=
    exists_section_power_complexity_bounds D hD J₀ I₀ hdisj₀ m J I mu hmu
      hdisj A hA
  obtain ⟨cIneq, hIneq⟩ := hineq
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cIneq a a
  refine ⟨2 * cRows + cFold, fun N => ?_⟩
  obtain ⟨x, hxlen, hxLower, hxUpper⟩ := hrows N
  have hApply := hIneq (a * N + a) x hxlen
  have hFoldN : (logSlack cIneq (a * N + a) : ℝ) ≤
      (logSlack cFold N : ℝ) := by
    exact_mod_cast hFold N
  calc
    (N : ℝ) * Real.logb 2 (maxSection A J₀ I₀) ≤
        ((tupleCondK D x J₀ I₀).toNat : ℝ) +
          (logSlack cRows N : ℝ) := hxLower
    _ ≤ (∑ k, mu k * ((tupleCondK D x (J k) (I k)).toNat : ℝ)) +
          (logSlack cFold N : ℝ) + (logSlack cRows N : ℝ) := by
      linarith
    _ ≤ (N : ℝ) *
          (∑ k, mu k * Real.logb 2 (maxSection A (J k) (I k))) +
          (logSlack cRows N : ℝ) + (logSlack cFold N : ℝ) +
          (logSlack cRows N : ℝ) := by
      linarith
    _ = (N : ℝ) *
          (∑ k, mu k * Real.logb 2 (maxSection A (J k) (I k))) +
          (logSlack (2 * cRows + cFold) N : ℝ) := by
      norm_num [logSlack]
      ring

private lemma le_of_mul_le_mul_add_logSlack (a b : ℝ) (c : ℕ)
    (h : ∀ N : ℕ, (N : ℝ) * a ≤ (N : ℝ) * b + (logSlack c N : ℝ)) :
    a ≤ b := by
  apply sub_nonpos.mp
  apply nonpos_of_mul_le_logSlack (a - b) c
  intro N
  have hN := h N
  nlinarith

/-- **Problem 283.**  A linear inequality `L ≤ R` between positive linear combinations of
(conditional or unconditional) complexities whose left-hand side `L` consists of a single term
corresponds to a true combinatorial inequality, under the translation
`C(x_J | x_I) ↦ log m_A(J | I)`, with `m_A(J | ∅) = m_A(J)` and `C(x_J | x_∅) = C(x_J)`
covering the unconditional terms.

The single left-hand term is an arbitrary one, `C(x_{J₀} | x_{I₀})` for disjoint `J₀, I₀`,
exactly as printed; its positive coefficient is absorbed by dividing the whole inequality by
it, so the left-hand coefficient is `1` here.  The book's own example is
`C(x₁, x₂) ≤ C(x₁) + C(x₂ | x₁)`, i.e. `J₀ = {1, 2}`, `I₀ = ∅`, whose counterpart is
`m(1, 2) ≤ m(1) · m(2 | 1)`.  SUV Problem 283, p. 317. -/
theorem logb_maxSection_le_sum_logb_maxSection (D : Map) (hD : isOptimalConditional D)
    (J₀ I₀ : Finset (Fin n)) (hdisj₀ : Disjoint J₀ I₀)
    (m : ℕ) (J I : Fin m → Finset (Fin n)) (mu : Fin m → ℝ) (hmu : ∀ k, 0 ≤ mu k)
    (hdisj : ∀ k, Disjoint (J k) (I k))
    (hineq : ∃ c : ℕ, ∀ (N : ℕ) (x : Fin n → BitString), tupleMaxLength x ≤ N →
        ((tupleCondK D x J₀ I₀).toNat : ℝ)
          ≤ (∑ k, mu k * ((tupleCondK D x (J k) (I k)).toNat : ℝ)) + (logSlack c N : ℝ))
    {Y : Fin n → Type} [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (A : Finset (∀ i, Y i)) (hA : A.Nonempty) :
    Real.logb 2 (maxSection A J₀ I₀)
      ≤ ∑ k, mu k * Real.logb 2 (maxSection A (J k) (I k)) := by
  obtain ⟨c, hc⟩ := exists_scaled_logb_maxSection_bound D hD J₀ I₀ hdisj₀ m J I
    mu hmu hdisj hineq A hA
  exact le_of_mul_le_mul_add_logSlack _ _ c hc

end Kolmogorov
