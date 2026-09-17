import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CanonicalImage
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Part03
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1RunBounds
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1RunCharging

/-!
# Naming a version of the run by its ordinal

`t1VersionDecoder` is the machine that turns a version ordinal into the model itself: from a
header carrying `n`, `k`, `epsilon` and the ordinal, it searches for the first stage at which
that version appears and returns its code.  `t1VersionDecoder_partrec` and
`t1VersionDecoder_eval` are its correctness, and `t1VersionDecoder_search_terminates_of_seen`
and `t1RunAt_version_getD_eq_of_le` justify the search — a version, once it has appeared, is
stable at every later stage.  `t1RunAt_versions_computable_uniform` makes the version list
computable uniformly in the run parameters.

This is what makes a version cheap to describe: `T1RunComplexity` combines it with a bound on
the ordinal to bound the plain set complexity of every reachable version.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/- Keep the nested encodings opaque while composing the uniform run with the
parser and unbounded search. -/
attribute [local irreducible] Primcodable.prod Primcodable.list

/-- Once a version has appeared in a reachable run, its contents are stable at
all later stages. -/
theorem t1RunAt_version_getD_eq_of_le
    (c : Code) (cDesc cSparse n k epsilon quota : Nat)
    {t t' version : Nat}
    (htt' : t ≤ t')
    (hv : version <
      (t1RunAt c cDesc cSparse n k epsilon quota t).versions.length) :
    (t1RunAt c cDesc cSparse n k epsilon quota t').versions.getD version [] =
      (t1RunAt c cDesc cSparse n k epsilon quota t).versions.getD version [] := by
  exact StagedEnumeration.getD_eq_of_prefix _ _
    (t1RunAt_versions_prefix c cDesc cSparse n k epsilon quota htt')
    version [] hv

/-- If a version has already appeared, unbounded search for the first stage at
which it appears terminates. -/
theorem t1VersionDecoder_search_terminates_of_seen
    (c : Code) (cDesc cSparse n k epsilon t version : Nat)
    (hv : version <
      (t1RunAt c cDesc cSparse n k epsilon
        (2 ^ (k - epsilon)) t).versions.length) :
    (Nat.rfind fun m =>
      Part.some (decide (version <
        (t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon)) m).versions.length))).Dom := by
  let p : ℕ →. Bool := fun m =>
    Part.some (decide (version <
      (t1RunAt c cDesc cSparse n k epsilon
        (2 ^ (k - epsilon)) m).versions.length))
  have hd : (Nat.rfind p).Dom := by
    rw [Nat.rfind_dom]
    refine ⟨t, ?_, fun {_} _ => Part.some_dom _⟩
    exact Part.mem_some_iff.mpr (decide_eq_true hv).symm
  exact hd

/-- The historical-version list is computable uniformly in all run
parameters. -/
theorem t1RunAt_versions_computable_uniform :
    Computable (fun input : T1RunInput => input.run.versions) := by
  have ht : Primrec (fun s : T1RunState => s.toProd) :=
    Primrec.of_equiv
  have hv : Primrec
      (fun p : T1RunStateData => p.2.2.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.snd)))))
  exact (hv.comp ht).to_comp.comp t1RunAt_computable_uniform

/-- Decoder for the versions of the T1 run: from a header carrying `n`, `k`, `epsilon` and a
version index it searches for the first time at which that version exists and outputs the
code of the corresponding model. -/
noncomputable def t1VersionDecoder
    (c : Code) (cDesc cSparse : Nat) :
    BitString →. BitString := fun input => do
  let header := decodeListCode (decodeFirst input)
  let n := bitsToNat (header.getD 0 [])
  let k := bitsToNat (header.getD 1 [])
  let epsilon := bitsToNat (header.getD 2 [])
  let version := bitsToNat (decodeSecond input)
  let quota := 2 ^ (k - epsilon)
  let t ← Nat.rfind fun m =>
    Part.some (decide (version < (t1RunAt c cDesc cSparse n k epsilon quota m).versions.length))
  let L := (t1RunAt c cDesc cSparse n k epsilon quota t).versions.getD version []
  Part.some (canonicalImageCodeOfList L)

/-- The version list extracted from run parameters in encoded input and time `p.2`
is computable. -/
private theorem t1RunAt_versions_computable_input (c : Code) (cDesc cSparse : Nat) :
    Computable (fun p : BitString × Nat =>
      (t1RunAt c cDesc cSparse
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 0 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []))
        (2 ^ (bitsToNat
          ((decodeListCode (decodeFirst p.1)).getD 1 []) -
            bitsToNat
              ((decodeListCode (decodeFirst p.1)).getD 2 [])))
        p.2).versions) := by
  have hheader : Computable (fun input : BitString =>
      decodeListCode (decodeFirst input)) :=
    decodeListCode_computable.comp decodeFirst_computable
  have hget : Computable₂
      (fun (l : List BitString) (i : Nat) => l.getD i []) :=
    (Primrec.list_getD []).to_comp
  have hn : Computable (fun input : BitString =>
      bitsToNat ((decodeListCode (decodeFirst input)).getD 0 [])) :=
    bitsToNat_primrec.to_comp.comp
      (hget.comp hheader (Computable.const 0))
  have hk : Computable (fun input : BitString =>
      bitsToNat ((decodeListCode (decodeFirst input)).getD 1 [])) :=
    bitsToNat_primrec.to_comp.comp
      (hget.comp hheader (Computable.const 1))
  have hepsilon : Computable (fun input : BitString =>
      bitsToNat ((decodeListCode (decodeFirst input)).getD 2 [])) :=
    bitsToNat_primrec.to_comp.comp
      (hget.comp hheader (Computable.const 2))
  have hquota : Computable (fun input : BitString =>
      2 ^ (bitsToNat ((decodeListCode (decodeFirst input)).getD 1 []) -
        bitsToNat ((decodeListCode (decodeFirst input)).getD 2 []))) :=
    primrec_two_pow_aux.to_comp.comp
      (Primrec.nat_sub.to_comp.comp hk hepsilon)
  let Data :=
    ((Code × Nat) × (Nat × Nat)) ×
      ((Nat × Nat) × (Nat × Nat))
  have hofData : Computable (fun p : Data =>
      ({ c := p.1.1.1
       , cDesc := p.1.1.2
       , cSparse := p.1.2.1
       , n := p.1.2.2
       , k := p.2.1.1
       , epsilon := p.2.1.2
       , quota := p.2.2.1
       , t := p.2.2.2 } : T1RunInput)) :=
    Primrec.of_equiv_symm.to_comp
  have hinput : Computable (fun p : BitString × Nat =>
      ({ c := c
       , cDesc := cDesc
       , cSparse := cSparse
       , n := bitsToNat
          ((decodeListCode (decodeFirst p.1)).getD 0 [])
       , k := bitsToNat
          ((decodeListCode (decodeFirst p.1)).getD 1 [])
       , epsilon := bitsToNat
          ((decodeListCode (decodeFirst p.1)).getD 2 [])
       , quota := 2 ^ (bitsToNat
          ((decodeListCode (decodeFirst p.1)).getD 1 []) -
            bitsToNat
              ((decodeListCode (decodeFirst p.1)).getD 2 []))
       , t := p.2 } : T1RunInput)) :=
    hofData.comp
      ((((Computable.const c).pair (Computable.const cDesc)).pair
          ((Computable.const cSparse).pair
            (hn.comp Computable.fst))).pair
        (((hk.comp Computable.fst).pair
            (hepsilon.comp Computable.fst)).pair
          ((hquota.comp Computable.fst).pair Computable.snd)))
  exact (t1RunAt_versions_computable_uniform.comp hinput).of_eq
    (fun _ => rfl)

/-- Unbounded search for the first stage reaching the target version is partial recursive. -/
private theorem t1VersionDecoder_find_partrec (c : Code) (cDesc cSparse : Nat) :
    Partrec (fun input : BitString =>
      Nat.rfind fun m =>
        Part.some (decide (bitsToNat (decodeSecond input) <
          (t1RunAt c cDesc cSparse
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 0 []))
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 1 []))
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 2 []))
            (2 ^ (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 1 []) -
                bitsToNat
                  ((decodeListCode (decodeFirst input)).getD 2 [])))
            m).versions.length))) := by
  have hversion : Computable (fun input : BitString =>
      bitsToNat (decodeSecond input)) :=
    bitsToNat_primrec.to_comp.comp decodeSecond_computable
  have hruns := t1RunAt_versions_computable_input c cDesc cSparse
  have hversionR : Computable (fun p : BitString × Nat =>
      bitsToNat (decodeSecond p.1)) :=
    hversion.comp Computable.fst
  have hlength : Computable (fun p : BitString × Nat =>
      (t1RunAt c cDesc cSparse
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 0 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []))
        (2 ^ (bitsToNat
          ((decodeListCode (decodeFirst p.1)).getD 1 []) -
            bitsToNat
              ((decodeListCode (decodeFirst p.1)).getD 2 [])))
        p.2).versions.length) :=
    Computable.list_length.comp hruns
  have hlt : Computable₂
      (fun a b : Nat => decide (a < b)) :=
    (PrimrecPred.decide Primrec.nat_lt).to_comp
  have hcheck : Computable₂
      (fun (input : BitString) (m : Nat) =>
        decide (bitsToNat (decodeSecond input) <
          (t1RunAt c cDesc cSparse
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 0 []))
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 1 []))
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 2 []))
            (2 ^ (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 1 []) -
                bitsToNat
                  ((decodeListCode (decodeFirst input)).getD 2 [])))
            m).versions.length)) :=
    hlt.comp hversionR hlength
  exact Partrec.rfind hcheck.partrec₂

/-- Extraction and encoding of the model for the version found at step `m` is computable. -/
private theorem t1VersionDecoder_post_computable (c : Code) (cDesc cSparse : Nat) :
    Computable₂
      (fun (input : BitString) (m : Nat) =>
        canonicalImageCodeOfList
          ((t1RunAt c cDesc cSparse
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 0 []))
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 1 []))
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 2 []))
            (2 ^ (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 1 []) -
                bitsToNat
                  ((decodeListCode (decodeFirst input)).getD 2 [])))
            m).versions.getD
              (bitsToNat (decodeSecond input)) [])) := by
  have hversion : Computable (fun input : BitString =>
      bitsToNat (decodeSecond input)) :=
    bitsToNat_primrec.to_comp.comp decodeSecond_computable
  have hruns := t1RunAt_versions_computable_input c cDesc cSparse
  have hversionR : Computable (fun p : BitString × Nat =>
      bitsToNat (decodeSecond p.1)) :=
    hversion.comp Computable.fst
  have hgetVersion : Computable₂
      (fun (l : List (List BitString)) (i : Nat) =>
        l.getD i []) :=
    (Primrec.list_getD []).to_comp
  have hlist : Computable (fun p : BitString × Nat =>
      (t1RunAt c cDesc cSparse
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 0 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []))
        (2 ^ (bitsToNat
          ((decodeListCode (decodeFirst p.1)).getD 1 []) -
            bitsToNat
              ((decodeListCode (decodeFirst p.1)).getD 2 [])))
        p.2).versions.getD
          (bitsToNat (decodeSecond p.1)) []) :=
    hgetVersion.comp hruns hversionR
  exact (canonicalImageCodeOfList_computable.comp hlist).to₂

/-- The version decoder is partial recursive. -/
theorem t1VersionDecoder_partrec
    (c : Code) (cDesc cSparse : Nat) :
    Partrec (t1VersionDecoder c cDesc cSparse) := by
  have hfind := t1VersionDecoder_find_partrec c cDesc cSparse
  have hpost := t1VersionDecoder_post_computable c cDesc cSparse
  exact (Partrec.bind hfind hpost.partrec₂).of_eq
    (fun _ => rfl)

/-- On the version program of a version index that is reached by time `t` and fits in the width
budget, the version decoder outputs the code of that version's model. -/
theorem t1VersionDecoder_eval
    (c : Code) (cDesc cSparse cWidth n k epsilon t version : Nat)
    (hseen : version <
      (t1RunAt c cDesc cSparse n k epsilon
        (2 ^ (k - epsilon)) t).versions.length)
    (hwidth : version <
      2 ^ (epsilon + logSlack cWidth n)) :
    canonicalImageCodeOfList
        ((t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon)) t).versions.getD version [])
      ∈ t1VersionDecoder c cDesc cSparse
          (t1VersionProgram cWidth n k epsilon version) := by
  obtain ⟨hheader, hversion⟩ :=
    t1VersionProgram_roundtrip
      cWidth n k epsilon version hwidth
  have hnparse : bitsToNat
      ((decodeListCode (decodeFirst
        (t1VersionProgram cWidth n k epsilon version))).getD
          0 []) = n := by
    rw [hheader]
    simp [bitsToNat_bits]
  have hkparse : bitsToNat
      ((decodeListCode (decodeFirst
        (t1VersionProgram cWidth n k epsilon version))).getD
          1 []) = k := by
    rw [hheader]
    simp [bitsToNat_bits]
  have heparse : bitsToNat
      ((decodeListCode (decodeFirst
        (t1VersionProgram cWidth n k epsilon version))).getD
          2 []) = epsilon := by
    rw [hheader]
    simp [bitsToNat_bits]
  let run := fun m =>
    t1RunAt c cDesc cSparse n k epsilon
      (2 ^ (k - epsilon)) m
  let hex : ∃ m, version < (run m).versions.length :=
    ⟨t, hseen⟩
  let t0 := Nat.find hex
  have ht0 : version < (run t0).versions.length :=
    Nat.find_spec hex
  have ht0_le : t0 ≤ t :=
    Nat.find_min' hex hseen
  let p : ℕ →. Bool := fun m =>
      Part.some
        (decide (version < (run m).versions.length))
  have hfind : Nat.rfind p = Part.some t0 := by
    rw [Part.eq_some_iff, Nat.mem_rfind]
    exact ⟨Part.mem_some_iff.mpr (decide_eq_true ht0).symm, fun {m} hm => by
      have : ¬ (version < (run m).versions.length) := Nat.find_min hex hm
      exact Part.mem_some_iff.mpr (decide_eq_false this).symm⟩
  have hget :
      (run t).versions.getD version [] =
        (run t0).versions.getD version [] := by
    exact t1RunAt_version_getD_eq_of_le
      c cDesc cSparse n k epsilon (2 ^ (k - epsilon))
      ht0_le ht0
  unfold t1VersionDecoder
  simp only [hnparse, hkparse, heparse, hversion]
  change canonicalImageCodeOfList
      ((t1RunAt c cDesc cSparse n k epsilon
        (2 ^ (k - epsilon)) t).versions.getD version []) ∈
    (Nat.rfind (fun m => Part.some (decide (version <
      (t1RunAt c cDesc cSparse n k epsilon
        (2 ^ (k - epsilon)) m).versions.length)))).bind
      (fun m => Part.some (canonicalImageCodeOfList
        ((t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon)) m).versions.getD version [])))
  rw [Part.mem_bind_iff]
  refine ⟨t0, ?_, ?_⟩
  · exact hfind ▸ ⟨trivial, rfl⟩
  · exact
      ⟨trivial, congrArg canonicalImageCodeOfList hget.symm⟩

end Kolmogorov
