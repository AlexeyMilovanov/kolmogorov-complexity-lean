import KolmogorovMathlib.Complexity.Information.MutualInformation
import KolmogorovMathlib.Multisource.Requests
import Mathlib.Computability.Halting

/-!
# Information distance and simultaneous encoding: Part 1
Theorems 232 and 233 prove sufficiency by colouring an enumerable bipartite graph.
The statements retain the produced off-by-one lengths. SUV Section 12.6, pp. 377–379.
-/

namespace Kolmogorov
/-- The Figure 41 request: inputs, an encoder, a capacity-`k` channel, and two output nodes.
All other channels are unlimited. SUV Figure 41, p. 377. -/
def informationDistanceRequest (A B : BitString) (k : ℕ) : InformationRequest (Fin 6) where
  edges := {(0, 2), (1, 2), (2, 3), (3, 4), (3, 5), (0, 4), (1, 5)}
  rank v := if v.val ≤ 1 then 0 else v.val - 1
  rank_lt := by decide +kernel
  capacity e := if e = (2, 3) then (k : ℕ∞) else ⊤
  input v := if v = 0 then some A else if v = 1 then some B else none
  output v := if v = 4 then some B else if v = 5 then some A else none
/-- The Figure 44 cut has capacity `k`, input `A`, and output `B`, giving `C(B|A) ≤ k`.
SUV Problem 327, p. 384. -/
theorem informationDistanceRequest_cut (A B : BitString) (k : ℕ) :
    (informationDistanceRequest A B k).cutCapacity {0, 3, 4} = (k : ℕ∞) ∧
      (informationDistanceRequest A B k).cutInputs {0, 3, 4} = [A] ∧
      (informationDistanceRequest A B k).cutOutputs {0, 3, 4} = [B] := by
  have hs : ({0, 3, 4} : Finset (Fin 6)).sort (· ≤ ·) = [0, 3, 4] := by
    simpa using (List.toFinset_sort (r := (· ≤ ·)) (l := [0, 3, 4]) (by simp)).2 (by simp)
  have he : (informationDistanceRequest A B k).cutEdges {0, 3, 4} = {(2, 3)} := by
    change (({(0, 2), (1, 2), (2, 3), (3, 4), (3, 5), (0, 4), (1, 5)} :
      Finset (Fin 6 × Fin 6)).filter fun e =>
        e.1 ∉ ({0, 3, 4} : Finset (Fin 6)) ∧ e.2 ∈ ({0, 3, 4} : Finset (Fin 6))) = _
    decide +kernel
  rw [InformationRequest.cutCapacity, he, InformationRequest.cutInputs,
    InformationRequest.cutOutputs, hs]
  simp [informationDistanceRequest]
/-- Helper. -/
def IsInformationDistanceColouring (D : Map)
    (colour : ℕ → BitString → BitString →. BitString) : Prop :=
  Partrec (fun q : (ℕ × BitString) × BitString => colour q.1.1 q.1.2 q.2) ∧
    ∀ (k : ℕ) (A B : BitString),
      condK D A B < (k : ℕ∞) → condK D B A < (k : ℕ∞) →
      ∃ X : BitString, X ∈ colour k A B ∧ X.length = k + 1 ∧
        (∀ B', X ∈ colour k A B' → B' = B) ∧
        ∀ A', X ∈ colour k A' B → A' = A
section PrefixColouring
open Nat.Partrec (Code)
private abbrev IdcEntry := (BitString × BitString) × BitString
/-- Helper. -/
def idcRun (c : Code) (s : ℕ) (p y : BitString) : Option BitString :=
  (Code.evaln s c (Encodable.encode (p, y))).bind fun r => Encodable.decode r
/-- Helper. -/
theorem idcRun_primrec (c : Code) :
    Primrec (fun a : ℕ × BitString × BitString => idcRun c a.1 a.2.1 a.2.2) :=
  Primrec.option_bind ((evaln_primrec c).comp Primrec.fst (Primrec.encode.comp Primrec.snd))
    (Primrec.decode.comp Primrec.snd).to₂
/-- Helper. -/
def idcShort (n : ℕ) : List BitString := (List.range n).flatMap exactLengthPrograms
/-- Helper. -/
theorem idcShort_primrec : Primrec idcShort :=
  Primrec.list_flatMap Primrec.list_range (primrec_exactLengthPrograms.comp Primrec.snd).to₂
/-- Helper. -/
theorem mem_idcShort {p : BitString} {n : ℕ} : p ∈ idcShort n ↔ p.length < n := by
  simp only [idcShort, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨m, hm, hp⟩; rw [exactLengthPrograms_length_eq m p hp]
    exact hm
  · intro h; exact ⟨p.length, h, mem_exactLengthPrograms_self p⟩
/-- Helper. -/
theorem length_idcShort (n : ℕ) : (idcShort n).length + 1 = 2 ^ n := by induction n with
  | zero => simp [idcShort]
  | succ n ih =>
    have h : idcShort (n + 1) = idcShort n ++ exactLengthPrograms n := by
      simp [idcShort, List.range_succ, List.flatMap_append]
    rw [h, List.length_append, length_exactLengthPrograms, pow_succ]
    omega
/-- Helper. -/
def idcBack (c : Code) (k s : ℕ) (A B : BitString) : Bool :=
  ((idcShort k).find? fun p => decide (idcRun c s p B = some A)).isSome
/-- Helper. -/
theorem idcBack_primrec (c : Code) :
    Primrec (fun a : (ℕ × ℕ) × BitString × BitString => idcBack c a.1.1 a.1.2 a.2.1 a.2.2) := by
  unfold idcBack
  refine Primrec.option_isSome.comp (list_find?_primrec
    (idcShort_primrec.comp (Primrec.fst.comp Primrec.fst)) ?_)
  refine (PrimrecRel.decide Primrec.eq).comp
    ((idcRun_primrec c).comp (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
    (Primrec.option_some.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
/-- Helper. -/
def idcEdgeOf (c : Code) (k s : ℕ) (A B : BitString) : Option (BitString × BitString) :=
  bif idcBack c k s A B then some (A, B) else none
/-- Helper. -/
theorem idcEdgeOf_primrec (c : Code) :
    Primrec (fun a : (ℕ × ℕ) × BitString × BitString => idcEdgeOf c a.1.1 a.1.2 a.2.1 a.2.2) :=
  Primrec.cond (idcBack_primrec c) (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
/-- Helper. -/
def idcEdgesAt (c : Code) (kl : ℕ × ℕ) (s : ℕ) : List (BitString × BitString) :=
  (boundedPrograms s).flatMap fun A => (idcShort kl.2).filterMap fun q =>
    (idcRun c s q A).bind (idcEdgeOf c kl.1 s A)
/-- Helper. -/
theorem idcEdgesAt_primrec (c : Code) :
    Primrec (fun a : (ℕ × ℕ) × ℕ => idcEdgesAt c a.1 a.2) := by
  have h3 : Primrec₂ (fun (d : (((ℕ × ℕ) × ℕ) × BitString) × BitString) (B : BitString) =>
      idcEdgeOf c d.1.1.1.1 d.1.1.2 d.1.2 B) :=
    ((idcEdgeOf_primrec c).comp (Primrec.pair (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))).to₂
  have h2 : Primrec₂ (fun (b : ((ℕ × ℕ) × ℕ) × BitString) (q : BitString) =>
      (idcRun c b.1.2 q b.2).bind (idcEdgeOf c b.1.1.1 b.1.2 b.2)) :=
    (Primrec.option_bind ((idcRun_primrec c).comp (Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)))) h3).to₂
  have h1 : Primrec₂ (fun (a : (ℕ × ℕ) × ℕ) (A : BitString) =>
      (idcShort a.1.2).filterMap fun q => (idcRun c a.2 q A).bind (idcEdgeOf c a.1.1 a.2 A)) :=
    (Primrec.listFilterMap (idcShort_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) h2).to₂
  exact Primrec.list_flatMap (primrec_boundedPrograms.comp Primrec.snd) h1
/-- Helper. -/
def idcEdgeHist (c : Code) (kl : ℕ × ℕ) (s : ℕ) : List (BitString × BitString) :=
  (List.range (s + 1)).flatMap (idcEdgesAt c kl)
/-- Helper. -/
theorem idcEdgeHist_primrec (c : Code) :
    Primrec (fun a : (ℕ × ℕ) × ℕ => idcEdgeHist c a.1 a.2) :=
  Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
    ((idcEdgesAt_primrec c).comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
/-- Helper. -/
def idcClash (l : ℕ) (e : BitString × BitString) (X : BitString) (x : IdcEntry) : Bool :=
  (decide (x.1.1 = e.1) && decide (x.2.take (l + 1) = X.take (l + 1))) ||
    (decide (x.1.2 = e.2) && decide (x.2 = X))
/-- Helper. -/
def idcPick (kl : ℕ × ℕ) (acc : List IdcEntry)
    (e : BitString × BitString) : Option BitString :=
  (exactLengthPrograms (kl.1 + 1)).find? fun X => !(acc.find? (idcClash kl.2 e X)).isSome
/-- Helper. -/
def idcExtend (kl : ℕ × ℕ) (acc : List IdcEntry)
    (e : BitString × BitString) : List IdcEntry :=
  ((idcPick kl acc e).map fun X => acc ++ [(e, X)]).getD acc
/-- Helper. -/
def idcSeen (acc : List IdcEntry) (e : BitString × BitString) : Bool :=
  (acc.find? fun x => decide (x.1 = e)).isSome
/-- Helper. -/
def idcStep (kl : ℕ × ℕ) (acc : List IdcEntry)
    (e : BitString × BitString) : List IdcEntry :=
  bif idcSeen acc e then acc else idcExtend kl acc e
/-- Helper. -/
def idcAssign (c : Code) (kl : ℕ × ℕ) (s : ℕ) : List IdcEntry :=
  (idcEdgeHist c kl s).foldl (idcStep kl) []
/-- Helper. -/
theorem idcClash_primrec : Primrec (fun a : ((ℕ × (BitString × BitString)) ×
    BitString) × IdcEntry => idcClash a.1.1.1 a.1.1.2 a.1.2 a.2) := by
  unfold idcClash
  have hl : Primrec (fun a : ((ℕ × (BitString × BitString)) × BitString) ×
      IdcEntry => a.1.1.1 + 1) :=
    Primrec.succ.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  refine Primrec.or.comp (Primrec.and.comp ?_ ?_) (Primrec.and.comp ?_ ?_)
  · exact (PrimrecRel.decide Primrec.eq).comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  · exact (PrimrecRel.decide Primrec.eq).comp
      (Primrec.list_take.comp hl (Primrec.snd.comp Primrec.snd))
      (Primrec.list_take.comp hl (Primrec.snd.comp Primrec.fst))
  · exact (PrimrecRel.decide Primrec.eq).comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  · exact (PrimrecRel.decide Primrec.eq).comp (Primrec.snd.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
/-- Helper. -/
theorem idcPick_primrec : Primrec (fun a : (ℕ × ℕ) ×
    List IdcEntry × (BitString × BitString) => idcPick a.1 a.2.1 a.2.2) := by
  have h2 : Primrec₂ (fun (b : ((ℕ × ℕ) × List IdcEntry ×
      (BitString × BitString)) × BitString) (x : IdcEntry) =>
        idcClash b.1.1.2 b.1.2.2 b.2 x) :=
    (idcClash_primrec.comp (Primrec.pair (Primrec.pair (Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.snd.comp Primrec.fst)) Primrec.snd)).to₂
  have h1 : Primrec₂ (fun (a : (ℕ × ℕ) × List IdcEntry ×
      (BitString × BitString)) (X : BitString) =>
        !(a.2.1.find? (idcClash a.1.2 a.2.2 X)).isSome) :=
    (Primrec.not.comp (Primrec.option_isSome.comp (list_find?_primrec
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) h2))).to₂
  exact list_find?_primrec (primrec_exactLengthPrograms.comp
    (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))) h1
/-- Helper. -/
theorem idcExtend_primrec : Primrec (fun a : (ℕ × ℕ) ×
    List IdcEntry × (BitString × BitString) => idcExtend a.1 a.2.1 a.2.2) := by
  have h : Primrec₂ (fun (a : (ℕ × ℕ) ×
      List IdcEntry × (BitString × BitString)) (X : BitString) =>
        a.2.1 ++ [(a.2.2, X)]) :=
    (Primrec.list_concat.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)).to₂
  exact Primrec.option_getD.comp (Primrec.option_map idcPick_primrec h)
    (Primrec.fst.comp Primrec.snd)
/-- Helper. -/
theorem idcSeen_primrec : Primrec (fun a : List IdcEntry × (BitString × BitString) =>
      idcSeen a.1 a.2) := by
  have h : Primrec₂ (fun (a : List IdcEntry ×
      (BitString × BitString)) (x : IdcEntry) => decide (x.1 = a.2)) :=
    ((PrimrecRel.decide Primrec.eq).comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)).to₂
  exact Primrec.option_isSome.comp (list_find?_primrec Primrec.fst h)
/-- Helper. -/
theorem idcStep_primrec : Primrec (fun a : (ℕ × ℕ) ×
    List IdcEntry × (BitString × BitString) => idcStep a.1 a.2.1 a.2.2) :=
  Primrec.cond (idcSeen_primrec.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
    idcExtend_primrec
/-- Helper. -/
theorem idcAssign_primrec (c : Code) :
    Primrec (fun a : (ℕ × ℕ) × ℕ => idcAssign c a.1 a.2) := by
  unfold idcAssign
  exact Primrec.list_foldl (idcEdgeHist_primrec c) (Primrec.const [])
    (idcStep_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))).to₂
/-- Helper. -/
theorem idcRun_sound {c : Code} {D : Map} (hc : IsCodeFor c D) {s : ℕ}
    {p y x : BitString} (h : idcRun c s p y = some x) : x ∈ D (p, y) := by
  unfold idcRun at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨r, hr, hx⟩ := h
  have h2 := Nat.Partrec.Code.evaln_sound hr
  rw [hc] at h2
  simp only [Encodable.encodek, Part.ofOption, Part.bind_some, Part.mem_map_iff] at h2
  obtain ⟨x', hx', rfl⟩ := h2
  rw [Encodable.encodek] at hx
  cases hx
  exact hx'
/-- Helper. -/
theorem idcRun_complete {c : Code} {D : Map} (hc : IsCodeFor c D)
    {p y x : BitString} (h : x ∈ D (p, y)) : ∃ s, idcRun c s p y = some x := by
  have h2 : Encodable.encode x ∈ c.eval (Encodable.encode (p, y)) := by
    rw [hc]
    simp only [Encodable.encodek, Part.ofOption, Part.bind_some]
    exact Part.mem_map _ h
  obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp h2
  refine ⟨s, ?_⟩
  unfold idcRun
  rw [Option.mem_def.mp hs]
  simp [Encodable.encodek]
/-- Helper. -/
theorem idcRun_mono {c : Code} {s s' : ℕ} {p y x : BitString}
    (h : idcRun c s p y = some x) (hs : s ≤ s') : idcRun c s' p y = some x := by
  unfold idcRun at h ⊢
  rw [Option.bind_eq_some_iff] at h ⊢
  obtain ⟨r, hr, hx⟩ := h
  exact ⟨r, Nat.Partrec.Code.evaln_mono hs hr, hx⟩
/-- Helper. -/
theorem idc_condK_lt_iff (D : Map) (x y : BitString) (n : ℕ) :
    condK D x y < (n : ℕ∞) ↔ ∃ p : BitString, p.length < n ∧ x ∈ D (p, y) := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt h)
    rw [← hm] at h
    obtain ⟨p, hp, hpx⟩ := (condK_le_iff D x y m).1 hm.symm.le
    exact ⟨p, lt_of_le_of_lt hp (by exact_mod_cast h), hpx⟩
  · rintro ⟨p, hp, hpx⟩
    exact lt_of_le_of_lt ((condK_le_iff D x y p.length).2 ⟨p, le_rfl, hpx⟩)
      (by exact_mod_cast hp)
/-- Helper. -/
def idcSep (l : ℕ) (x y : IdcEntry) : Prop :=
  x.1 ≠ y.1 ∧ (x.1.1 = y.1.1 → x.2.take (l + 1) ≠ y.2.take (l + 1)) ∧
    (x.1.2 = y.1.2 → x.2 ≠ y.2)
/-- Helper. -/
theorem idcSep_symm (l : ℕ) : ∀ ⦃x y : IdcEntry⦄, idcSep l x y → idcSep l y x :=
  fun _ _ h => ⟨h.1.symm, fun e => (h.2.1 e.symm).symm, fun e => (h.2.2 e.symm).symm⟩
/-- Helper. -/
def idcGraph (D : Map) (kl : ℕ × ℕ) (e : BitString × BitString) : Prop :=
  condK D e.1 e.2 < (kl.1 : ℕ∞) ∧ condK D e.2 e.1 < (kl.2 : ℕ∞)
/-- Helper. -/
theorem idcStep_prefix (kl : ℕ × ℕ) (acc : List IdcEntry)
    (e : BitString × BitString) : acc <+: idcStep kl acc e := by
  unfold idcStep idcExtend
  cases idcSeen acc e
  · cases idcPick kl acc e <;> simp
  · exact List.prefix_refl _
/-- Helper. -/
theorem mem_idcStep {kl : ℕ × ℕ} {acc : List IdcEntry}
    {e : BitString × BitString} {x : IdcEntry}
    (h : x ∈ idcStep kl acc e) : x ∈ acc ∨ (x.1 = e ∧ x.2.length = kl.1 + 1) := by
  unfold idcStep idcExtend at h
  cases hs : idcSeen acc e
  · cases hp : idcPick kl acc e with
    | none =>
      simp only [hs, hp, Bool.cond_false, Option.map_none, Option.getD_none] at h; exact Or.inl h
    | some X =>
      simp only [hs, hp, Bool.cond_false, Option.map_some, Option.getD_some, List.mem_append,
        List.mem_singleton] at h
      rcases h with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨rfl, exactLengthPrograms_length_eq _ _ (List.mem_of_find?_eq_some hp)⟩
  · simp only [hs, Bool.cond_true] at h; exact Or.inl h
/-- Helper. -/
theorem idcStep_pairwise {kl : ℕ × ℕ} {acc : List IdcEntry}
    {e : BitString × BitString} (h : acc.Pairwise (idcSep kl.2)) :
    (idcStep kl acc e).Pairwise (idcSep kl.2) := by
  unfold idcStep idcExtend
  cases hs : idcSeen acc e
  · cases hp : idcPick kl acc e with
    | none => simpa using h
    | some X =>
      simp only [Bool.cond_false, Option.map_some, Option.getD_some]
      refine List.pairwise_append.2 ⟨h, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
      rw [List.mem_singleton] at hy
      subst hy
      have hne : x.1 ≠ e := by
        intro hxe
        have : idcSeen acc e = true := List.find?_isSome.2 ⟨x, hx, by simp [hxe]⟩
        rw [hs] at this
        exact Bool.false_ne_true this
      have hX := List.find?_some hp
      have hnc : idcClash kl.2 e X x = false := by
        cases hc : idcClash kl.2 e X x
        · rfl
        · have : (acc.find? (idcClash kl.2 e X)).isSome := List.find?_isSome.2 ⟨x, hx, hc⟩
          simp [this] at hX
      simp only [idcClash, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at hnc
      exact ⟨hne, fun h1 h2 => hnc.1.elim (· h1) (· h2),
        fun h1 h2 => hnc.2.elim (· h1) (· h2)⟩
  · simpa using h
/-- Helper. -/
theorem idcFold_prefix (kl : ℕ × ℕ) :
    ∀ (L : List (BitString × BitString)) (acc : List IdcEntry), acc <+: L.foldl (idcStep kl) acc
  | [], _ => List.prefix_refl _
  | e :: L, acc => (idcStep_prefix kl acc e).trans (idcFold_prefix kl L _)
/-- Helper. -/
theorem idcFold_pairwise (kl : ℕ × ℕ) :
    ∀ (L : List (BitString × BitString)) (acc : List IdcEntry),
      acc.Pairwise (idcSep kl.2) → (L.foldl (idcStep kl) acc).Pairwise (idcSep kl.2)
  | [], _, h => h
  | _ :: L, _, h => idcFold_pairwise kl L _ (idcStep_pairwise h)
/-- Helper. -/
theorem mem_idcFold (kl : ℕ × ℕ) :
    ∀ (L : List (BitString × BitString)) (acc : List IdcEntry)
      (x : IdcEntry), x ∈ L.foldl (idcStep kl) acc → x ∈ acc ∨ (x.1 ∈ L ∧ x.2.length = kl.1 + 1)
  | [], _, _, h => Or.inl h
  | e :: L, acc, x, h => by
    rcases mem_idcFold kl L _ x h with h' | ⟨h1, h2⟩
    · rcases mem_idcStep h' with h'' | ⟨h1, h2⟩
      · exact Or.inl h''
      · exact Or.inr ⟨h1 ▸ List.mem_cons_self, h2⟩
    · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩
/-- Helper. -/
theorem idc_length_le_of_condK_lt (D : Map) (y : BitString) (n : ℕ)
    (L : List BitString) (hL : L.Nodup) (h : ∀ x ∈ L, condK D x y < (n : ℕ∞)) :
    L.length + 1 ≤ 2 ^ n := by
  classical
  have hex : ∀ x ∈ L, ∃ p : BitString, p.length < n ∧ x ∈ D (p, y) :=
    fun x hx => (idc_condK_lt_iff D x y n).1 (h x hx)
  let g : BitString → BitString := fun x => if hx : x ∈ L then (hex x hx).choose else []
  have hg : ∀ x ∈ L, (g x).length < n ∧ x ∈ D (g x, y) := by
    intro x hx
    simp only [g, dite_eq_left hx]
    exact (hex x hx).choose_spec
  have hcard : L.toFinset.card ≤ (idcShort n).toFinset.card := by
    refine Finset.card_le_card_of_injOn g (fun x hx => ?_) (fun x hx x' hx' hxx => ?_)
    · simp only [Finset.mem_coe, List.mem_toFinset] at hx ⊢
      exact mem_idcShort.2 (hg x hx).1
    · simp only [Finset.mem_coe, List.mem_toFinset] at hx hx'
      have h1 := (hg x hx).2
      have h2 := (hg x' hx').2
      rw [hxx] at h1
      exact Part.mem_unique h1 h2
  rw [List.toFinset_card_of_nodup hL] at hcard
  have := List.toFinset_card_le (idcShort n)
  have := length_idcShort n
  omega
/-- Helper. -/
theorem idc_filter_length (D : Map) {l n : ℕ} {y : BitString}
    {acc : List IdcEntry} (hsep : acc.Pairwise (idcSep l)) {p : IdcEntry → Bool}
    (f : IdcEntry → BitString) (hinj : ∀ a b, p a = true → p b = true → f a = f b → a.1 = b.1)
    (h : ∀ x ∈ acc, p x = true → condK D (f x) y < (n : ℕ∞)) :
    (acc.filter p).length + 1 ≤ 2 ^ n := by
  have := idc_length_le_of_condK_lt D y n ((acc.filter p).map f) (List.pairwise_map.2
    ((hsep.filter p).imp_of_mem fun ha hb hab heq =>
      hab.1 (hinj _ _ (List.mem_filter.1 ha).2 (List.mem_filter.1 hb).2 heq)))
    (fun x hx => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
      exact h z (List.mem_filter.1 hz).1 (List.mem_filter.1 hz).2)
  simpa using this
/-- Helper. -/
theorem idcPick_isSome (D : Map) {kl : ℕ × ℕ} (hkl : kl.2 ≤ kl.1)
    {acc : List IdcEntry} {e : BitString × BitString} (hsep : acc.Pairwise (idcSep kl.2))
    (hA : ∀ x ∈ acc, x.1.1 = e.1 → condK D x.1.2 e.1 < (kl.2 : ℕ∞))
    (hB : ∀ x ∈ acc, x.1.2 = e.2 → condK D x.1.1 e.2 < (kl.1 : ℕ∞)) :
    (idcPick kl acc e).isSome := by
  classical
  obtain ⟨k, l⟩ := kl
  simp only at hkl hA hB hsep ⊢
  by_contra hnone
  have hall : ∀ X ∈ exactLengthPrograms (k + 1), ∃ x ∈ acc, idcClash l e X x = true := by
    intro X hX
    by_contra hno
    push Not at hno
    apply hnone
    refine List.find?_isSome.2 ⟨X, hX, ?_⟩
    have : (acc.find? (idcClash l e X)).isSome = false := by
      cases h' : (acc.find? (idcClash l e X)).isSome
      · rfl
      · obtain ⟨x, hx, hc⟩ := List.find?_isSome.1 h'
        exact absurd hc (by simp [hno x hx])
    simp [this]
  set LA := acc.filter fun x => decide (x.1.1 = e.1)
  set LB := acc.filter fun x => decide (x.1.2 = e.2)
  set TA := (LA.map fun x => x.2.take (l + 1)).toFinset
  set TB := (LB.map fun x => x.2).toFinset
  have hsub : (exactLengthPrograms (k + 1)).toFinset ⊆
      TB ∪ (TA ×ˢ (exactLengthPrograms (k - l)).toFinset).image (fun p => p.1 ++ p.2) := by
    intro X hX
    rw [List.mem_toFinset] at hX
    obtain ⟨x, hx, hc⟩ := hall X hX
    have hXlen := exactLengthPrograms_length_eq _ _ hX
    simp only [idcClash, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Finset.mem_union_right _ (Finset.mem_image.2
        ⟨(X.take (l + 1), X.drop (l + 1)), ?_, List.take_append_drop _ _⟩)
      refine Finset.mem_product.2 ⟨?_, ?_⟩
      · simp only [TA, LA, List.mem_toFinset, List.mem_map]
        exact ⟨x, List.mem_filter.2 ⟨hx, by simp [h1]⟩, h2⟩
      · rw [List.mem_toFinset]
        have hd : (X.drop (l + 1)).length = k - l := by simp [hXlen]
        rw [← hd]
        exact mem_exactLengthPrograms_self _
    · refine Finset.mem_union_left _ ?_
      simp only [TB, LB, List.mem_toFinset, List.mem_map]
      exact ⟨x, List.mem_filter.2 ⟨hx, by simp [h1]⟩, h2⟩
  have hcardR := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (exactLengthPrograms_nodup _), length_exactLengthPrograms,
    pow_succ] at hcardR
  have hU := Finset.card_union_le TB
    ((TA ×ˢ (exactLengthPrograms (k - l)).toFinset).image (fun p => p.1 ++ p.2))
  have hI := Finset.card_image_le (s := TA ×ˢ (exactLengthPrograms (k - l)).toFinset)
    (f := fun p : BitString × BitString => p.1 ++ p.2)
  rw [Finset.card_product, List.toFinset_card_of_nodup (exactLengthPrograms_nodup _),
    length_exactLengthPrograms] at hI
  have hTA : TA.card ≤ LA.length := (List.toFinset_card_le _).trans (by simp)
  have hTB : TB.card ≤ LB.length := (List.toFinset_card_le _).trans (by simp)
  have hLA : LA.length + 1 ≤ 2 ^ l :=
    idc_filter_length D hsep (fun x => x.1.2) (fun a b ha hb h => Prod.ext
      ((of_decide_eq_true ha).trans (of_decide_eq_true hb).symm) h)
      (fun x hx h => hA x hx (of_decide_eq_true h))
  have hLB : LB.length + 1 ≤ 2 ^ k :=
    idc_filter_length D hsep (fun x => x.1.1) (fun a b ha hb h => Prod.ext h
      ((of_decide_eq_true ha).trans (of_decide_eq_true hb).symm))
      (fun x hx h => hB x hx (of_decide_eq_true h))
  have hP : 2 ^ l * 2 ^ (k - l) = 2 ^ k := by rw [← pow_add, Nat.add_sub_cancel' hkl]
  have hpos : 1 ≤ 2 ^ (k - l) := Nat.one_le_two_pow
  have h1 : (LA.length + 1) * 2 ^ (k - l) ≤ 2 ^ l * 2 ^ (k - l) := Nat.mul_le_mul_right _ hLA
  have h2 : TA.card * 2 ^ (k - l) ≤ LA.length * 2 ^ (k - l) := Nat.mul_le_mul_right _ hTA
  nlinarith
/-- Helper. -/
theorem idcStep_covers (D : Map) {kl : ℕ × ℕ} (hkl : kl.2 ≤ kl.1)
    {acc : List IdcEntry} {e : BitString × BitString}
    (hsep : acc.Pairwise (idcSep kl.2)) (hacc : ∀ x ∈ acc, idcGraph D kl x.1) :
    ∃ X, (e, X) ∈ idcStep kl acc e := by
  unfold idcStep
  cases hs : idcSeen acc e
  · have hp := idcPick_isSome D hkl (e := e) hsep (fun x hx h => by rw [← h]; exact (hacc x hx).2)
      (fun x hx h => by rw [← h]; exact (hacc x hx).1)
    obtain ⟨X, hX⟩ := Option.isSome_iff_exists.1 hp
    exact ⟨X, by simp [idcExtend, hX]⟩
  · obtain ⟨x, hx, hxe⟩ := List.find?_isSome.1 hs
    simp only [decide_eq_true_eq] at hxe
    exact ⟨x.2, by simpa [← hxe] using hx⟩
/-- Helper. -/
theorem idcFold_covers (D : Map) {kl : ℕ × ℕ} (hkl : kl.2 ≤ kl.1) :
    ∀ (L : List (BitString × BitString)) (acc : List IdcEntry),
      acc.Pairwise (idcSep kl.2) → (∀ x ∈ acc, idcGraph D kl x.1) →
      (∀ e ∈ L, idcGraph D kl e) → ∀ e ∈ L, ∃ X, (e, X) ∈ L.foldl (idcStep kl) acc
  | [], _, _, _, _, _, he => absurd he List.not_mem_nil
  | e' :: L, acc, hsep, hacc, hL, e, he => by
    have hsep' := idcStep_pairwise (e := e') hsep
    have hacc' : ∀ x ∈ idcStep kl acc e', idcGraph D kl x.1 := by
      intro x hx
      rcases mem_idcStep hx with h | ⟨h, -⟩
      · exact hacc x h
      · rw [h]
        exact hL e' List.mem_cons_self
    rcases List.mem_cons.1 he with rfl | he
    · obtain ⟨X, hX⟩ := idcStep_covers D hkl (e := e) hsep hacc
      exact ⟨X, (idcFold_prefix kl L _).subset hX⟩
    · exact idcFold_covers D hkl L _ hsep' hacc'
        (fun e he => hL e (List.mem_cons_of_mem _ he)) e he
/-- Helper. -/
theorem idcEdgeHist_sound {c : Code} {D : Map} (hc : IsCodeFor c D) {kl : ℕ × ℕ}
    {s : ℕ} {e : BitString × BitString} (he : e ∈ idcEdgeHist c kl s) : idcGraph D kl e := by
  simp only [idcEdgeHist, idcEdgesAt, List.mem_flatMap, List.mem_filterMap,
    Option.bind_eq_some_iff] at he
  obtain ⟨s', -, A, -, q, hq, B, hB, he⟩ := he
  unfold idcEdgeOf at he
  cases hb : idcBack c kl.1 s' A B
  · simp [hb] at he
  · simp only [hb, Bool.cond_true, Option.some.injEq] at he
    subst he
    obtain ⟨p, hp, hpB⟩ := List.find?_isSome.1 hb
    simp only [decide_eq_true_eq] at hpB
    exact ⟨(idc_condK_lt_iff D _ _ _).2 ⟨p, mem_idcShort.1 hp, idcRun_sound hc hpB⟩,
      (idc_condK_lt_iff D _ _ _).2 ⟨q, mem_idcShort.1 hq, idcRun_sound hc hB⟩⟩
/-- Helper. -/
theorem idcEdgeHist_complete {c : Code} {D : Map} (hc : IsCodeFor c D) {kl : ℕ × ℕ}
    {e : BitString × BitString} (he : idcGraph D kl e) : ∃ s, e ∈ idcEdgeHist c kl s := by
  obtain ⟨A, B⟩ := e
  obtain ⟨p, hp, hpA⟩ := (idc_condK_lt_iff D _ _ _).1 he.1
  obtain ⟨q, hq, hqB⟩ := (idc_condK_lt_iff D _ _ _).1 he.2
  obtain ⟨s1, hs1⟩ := idcRun_complete hc hpA
  obtain ⟨s2, hs2⟩ := idcRun_complete hc hqB
  refine ⟨s1 + s2 + A.length, ?_⟩
  simp only [idcEdgeHist, idcEdgesAt, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  refine ⟨s1 + s2 + A.length, by omega, A, (mem_boundedPrograms_iff A _).2 (by omega), q,
    mem_idcShort.2 hq, ?_⟩
  rw [idcRun_mono hs2 (by omega : s2 ≤ s1 + s2 + A.length)]
  have hb : idcBack c kl.1 (s1 + s2 + A.length) A B = true :=
    List.find?_isSome.2 ⟨p, mem_idcShort.2 hp,
      by simp [idcRun_mono hs1 (by omega : s1 ≤ s1 + s2 + A.length)]⟩
  simp [idcEdgeOf, hb]
/-- Helper. -/
theorem idcEdgeHist_prefix (c : Code) (kl : ℕ × ℕ) {s s' : ℕ} (h : s ≤ s') :
    idcEdgeHist c kl s <+: idcEdgeHist c kl s' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have e : List.range (s + d + 1) = List.range (s + 1) ++ (List.range d).map (s + 1 + ·) := by
    rw [show s + d + 1 = (s + 1) + d by omega]
    exact List.range_add
  unfold idcEdgeHist
  rw [e, List.flatMap_append]
  exact List.prefix_append _ _
/-- Helper. -/
theorem idcAssign_prefix (c : Code) (kl : ℕ × ℕ) {s s' : ℕ} (h : s ≤ s') :
    idcAssign c kl s <+: idcAssign c kl s' := by
  obtain ⟨M, hM⟩ := idcEdgeHist_prefix c kl h
  unfold idcAssign
  rw [← hM, List.foldl_append]
  exact idcFold_prefix kl M _
/-- Helper. -/
theorem idcAssign_pairwise (c : Code) (kl : ℕ × ℕ) (s : ℕ) :
    (idcAssign c kl s).Pairwise (idcSep kl.2) :=
  idcFold_pairwise kl _ [] List.Pairwise.nil
/-- Helper. -/
theorem idcAssign_length {c : Code} {kl : ℕ × ℕ} {s : ℕ}
    {x : IdcEntry} (h : x ∈ idcAssign c kl s) : x.2.length = kl.1 + 1 :=
  ((mem_idcFold kl _ [] x h).resolve_left List.not_mem_nil).2
/-- Helper. -/
theorem idcAssign_covers {c : Code} {D : Map} (hc : IsCodeFor c D) {kl : ℕ × ℕ}
    (hkl : kl.2 ≤ kl.1) {e : BitString × BitString} (he : idcGraph D kl e) :
    ∃ s X, (e, X) ∈ idcAssign c kl s := by
  obtain ⟨s, hs⟩ := idcEdgeHist_complete hc he
  obtain ⟨X, hX⟩ := idcFold_covers D hkl _ [] List.Pairwise.nil (by simp)
    (fun e' he' => idcEdgeHist_sound hc he') e hs
  exact ⟨s, X, hX⟩
/-- Helper. -/
def idcMatch (mode l : ℕ) (u v : BitString) (x : IdcEntry) : Bool :=
  bif decide (mode = 0) then decide (x.1.1 = u) && decide (x.1.2 = v)
  else bif decide (mode = 1) then decide (x.1.2 = u) && decide (x.2 = v)
  else decide (x.1.1 = u) && decide (x.2.take (l + 1) = v)
/-- Helper. -/
def idcOut (mode : ℕ) (x : IdcEntry) : BitString :=
  bif decide (mode = 0) then x.2 else bif decide (mode = 1) then x.1.1 else x.1.2
/-- Helper. -/
def idcQuery (c : Code) (mode : ℕ) (kl : ℕ × ℕ) (uv : BitString × BitString)
    (s : ℕ) : Option BitString :=
  ((idcAssign c kl s).find? (idcMatch mode kl.2 uv.1 uv.2)).map (idcOut mode)
/-- Helper. -/
def idcFind (c : Code) (mode : ℕ) (kl : ℕ × ℕ) (uv : BitString × BitString) :
    Part BitString :=
  (Nat.rfind fun s => Part.some (idcQuery c mode kl uv s).isSome).bind fun s =>
    Part.ofOption (idcQuery c mode kl uv s)
/-- Helper. -/
def idcMap (c : Code) (mode : ℕ) : Map := fun pr =>
  idcFind c mode (decodeBits (decodeFirst pr.1), decodeBits (decodeSecond pr.1))
    (decodeFirst pr.2, decodeSecond pr.2)
/-- Helper. -/
theorem idcMatch_primrec (mode : ℕ) : Primrec (fun a : (ℕ × BitString × BitString) ×
    IdcEntry => idcMatch mode a.1.1 a.1.2.1 a.1.2.2 a.2) := by
  unfold idcMatch
  have dec := PrimrecRel.decide (Primrec.eq (α := BitString))
  have hu := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst (α := ℕ × BitString × BitString)
    (β := IdcEntry)))
  have hv := Primrec.snd.comp (Primrec.snd.comp (Primrec.fst (α := ℕ × BitString × BitString)
    (β := IdcEntry)))
  refine Primrec.cond (Primrec.const _) (Primrec.and.comp (dec.comp
    (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) hu) (dec.comp
    (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) hv)) (Primrec.cond (Primrec.const _)
    (Primrec.and.comp (dec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) hu)
      (dec.comp (Primrec.snd.comp Primrec.snd) hv))
    (Primrec.and.comp (dec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) hu)
      (dec.comp (Primrec.list_take.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd)) hv)))
/-- Helper. -/
theorem idcOut_primrec (mode : ℕ) : Primrec (idcOut mode) := by
  unfold idcOut
  exact Primrec.cond (Primrec.const _) Primrec.snd
    (Primrec.cond (Primrec.const _) (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
/-- Helper. -/
theorem idcQuery_primrec (c : Code) (mode : ℕ) :
    Primrec (fun a : ((ℕ × ℕ) × (BitString × BitString)) × ℕ =>
      idcQuery c mode a.1.1 a.1.2 a.2) := by
  have h : Primrec₂ (fun (a : ((ℕ × ℕ) × (BitString × BitString)) × ℕ)
      (x : IdcEntry) => idcMatch mode a.1.1.2 a.1.2.1 a.1.2.2 x) :=
    ((idcMatch_primrec mode).comp (Primrec.pair (Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)).to₂
  have hp : Primrec (fun a : ((ℕ × ℕ) × (BitString × BitString)) × ℕ => (a.1.1, a.2)) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hA : Primrec (fun a : ((ℕ × ℕ) × (BitString × BitString)) × ℕ =>
      idcAssign c a.1.1 a.2) :=
    ((idcAssign_primrec c).comp hp :)
  have hf : Primrec (fun a : ((ℕ × ℕ) × (BitString × BitString)) × ℕ =>
      (idcAssign c a.1.1 a.2).find? (idcMatch mode a.1.1.2 a.1.2.1 a.1.2.2)) :=
    list_find?_primrec hA h
  exact (Primrec.option_map hf ((idcOut_primrec mode).comp Primrec.snd).to₂).of_eq
    fun _ => rfl
/-- Helper. -/
theorem idcFind_partrec (c : Code) (mode : ℕ) :
    Partrec (fun a : (ℕ × ℕ) × (BitString × BitString) => idcFind c mode a.1 a.2) := by
  have h1 : Computable (fun a : ((ℕ × ℕ) × (BitString × BitString)) × ℕ =>
      idcQuery c mode a.1.1 a.1.2 a.2) := (idcQuery_primrec c mode).to_comp
  have h2 : Computable₂ (fun (a : (ℕ × ℕ) × (BitString × BitString)) (s : ℕ) =>
      (idcQuery c mode a.1 a.2 s).isSome) :=
    Primrec.option_isSome.to_comp.comp h1
  exact Partrec.bind (Partrec.rfind h2.partrec₂) (Computable.ofOption h1).to₂
/-- Helper. -/
def idcColourArg (q : (ℕ × BitString) × BitString) :
    (ℕ × ℕ) × (BitString × BitString) := ((q.1.1, q.1.1), (q.1.2, q.2))
/-- Helper. -/
theorem idcColourArg_primrec : Primrec idcColourArg := by
  unfold idcColourArg
  let hf : Primrec (fun q : (ℕ × BitString) × BitString => q.1) := Primrec.fst
  exact Primrec.pair (Primrec.pair (Primrec.fst.comp hf) (Primrec.fst.comp hf))
    (Primrec.pair (Primrec.snd.comp hf) Primrec.snd)
/-- Helper. -/
theorem idcColour_partrec (c : Code) : Partrec (fun q =>
    idcFind c 0 (idcColourArg q).1 (idcColourArg q).2) :=
  (idcFind_partrec c 0).comp idcColourArg_primrec.to_comp
/-- Helper. -/
theorem idcMap_partrec (c : Code) (mode : ℕ) : Partrec (idcMap c mode) := by
  have hp : Computable (fun pr : BitString × BitString =>
      ((decodeBits (decodeFirst pr.1), decodeBits (decodeSecond pr.1)),
        (decodeFirst pr.2, decodeSecond pr.2))) :=
    Computable.pair (Computable.pair
      (primrec_decodeBits.to_comp.comp (decodeFirst_computable.comp Computable.fst))
      (primrec_decodeBits.to_comp.comp (decodeSecond_computable.comp Computable.fst)))
      (Computable.pair (decodeFirst_computable.comp Computable.snd)
        (decodeSecond_computable.comp Computable.snd))
  exact ((idcFind_partrec c mode).comp hp).of_eq fun _ => rfl
/-- Helper. -/
theorem idcMatch_unique (mode l : ℕ) (u v : BitString) {x y : IdcEntry} (hxy : idcSep l x y)
    (hx : idcMatch mode l u v x = true) (hy : idcMatch mode l u v y = true) : False := by
  unfold idcMatch at hx hy
  rcases Nat.lt_trichotomy mode 1 with h | rfl | h
  · obtain rfl : mode = 0 := by omega
    simp only [decide_true, Bool.cond_true, Bool.and_eq_true, decide_eq_true_eq] at hx hy
    exact hxy.1 (Prod.ext (hx.1.trans hy.1.symm) (hx.2.trans hy.2.symm))
  · simp only [Nat.one_ne_zero, decide_false, Bool.cond_false, decide_true, Bool.cond_true,
      Bool.and_eq_true, decide_eq_true_eq] at hx hy
    exact hxy.2.2 (hx.1.trans hy.1.symm) (hx.2.trans hy.2.symm)
  · have h0 : mode ≠ 0 := by omega
    have h1 : mode ≠ 1 := by omega
    simp only [h0, h1, decide_false, Bool.cond_false, Bool.and_eq_true, decide_eq_true_eq] at hx hy
    exact hxy.2.1 (hx.1.trans hy.1.symm) (hx.2.trans hy.2.symm)
/-- Helper. -/
theorem idcFind_spec {c : Code} {mode : ℕ} {kl : ℕ × ℕ} {uv : BitString × BitString}
    {s0 : ℕ} {x0 : IdcEntry} (hx0 : x0 ∈ idcAssign c kl s0)
    (hm : idcMatch mode kl.2 uv.1 uv.2 x0 = true) : idcOut mode x0 ∈ idcFind c mode kl uv := by
  have hex : ∃ s, (idcQuery c mode kl uv s).isSome := ⟨s0, by
    unfold idcQuery
    rw [Option.isSome_map]
    exact List.find?_isSome.2 ⟨x0, hx0, hm⟩⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (Nat.find_spec hex)
  have hr' := hr
  unfold idcQuery at hr'
  rw [Option.map_eq_some_iff] at hr'
  obtain ⟨x, hx, hxr⟩ := hr'
  have hxm := List.find?_some hx
  have hxmem := List.mem_of_find?_eq_some hx
  have hxy : x = x0 := by
    by_contra hne
    have h1 := (idcAssign_prefix c kl (le_max_left (Nat.find hex) s0)).subset hxmem
    have h2 := (idcAssign_prefix c kl (le_max_right (Nat.find hex) s0)).subset hx0
    let _ : Std.Symm (idcSep kl.2) := ⟨idcSep_symm kl.2⟩
    exact idcMatch_unique mode kl.2 uv.1 uv.2
      ((idcAssign_pairwise c kl _).forall h1 h2 hne) hxm hm
  unfold idcFind
  rw [Part.mem_bind_iff]
  refine ⟨Nat.find hex, ?_, ?_⟩
  · refine Nat.mem_rfind.2 ⟨by simpa using Nat.find_spec hex, fun {m} hm' => ?_⟩
    simpa using Nat.find_min hex hm'
  · rw [hr, ← hxr, hxy]; exact Part.mem_some _
/-- Helper. -/
theorem idcFind_mem {c : Code} {mode : ℕ} {kl : ℕ × ℕ}
    {uv : BitString × BitString} {out : BitString} (h : out ∈ idcFind c mode kl uv) :
    ∃ s x, x ∈ idcAssign c kl s ∧ idcMatch mode kl.2 uv.1 uv.2 x = true ∧
      idcOut mode x = out := by
  unfold idcFind at h
  rcases Part.mem_bind_iff.1 h with ⟨s, -, hs⟩
  rw [Part.mem_ofOption, Option.mem_def] at hs
  unfold idcQuery at hs
  obtain ⟨x, hx, hout⟩ := Option.map_eq_some_iff.1 hs
  exact ⟨s, x, List.mem_of_find?_eq_some hx, List.find?_some hx, hout⟩
/-- Helper. -/
theorem idcFind_zero_unique {c : Code} {k : ℕ} {A B A' B' X : BitString}
    (h : X ∈ idcFind c 0 (k, k) (A, B)) (h' : X ∈ idcFind c 0 (k, k) (A', B'))
    (hend : A = A' ∨ B = B') : (A, B) = (A', B') := by
  obtain ⟨s, ⟨⟨a, b⟩, Y⟩, he, hm, ho⟩ := idcFind_mem h
  obtain ⟨s', ⟨⟨a', b'⟩, Y'⟩, he', hm', ho'⟩ := idcFind_mem h'
  simp only [idcMatch, decide_true, Bool.cond_true, Bool.and_eq_true, decide_eq_true_eq,
    idcOut] at hm hm' ho ho'
  rcases hm with ⟨rfl, rfl⟩; rcases hm' with ⟨rfl, rfl⟩
  subst Y; subst Y'
  by_contra hne
  have hne' : ((a, b), X) ≠ ((a', b'), X) := fun h => hne (congrArg Prod.fst h)
  let _ : Std.Symm (idcSep k) := ⟨idcSep_symm k⟩
  have hsep := (idcAssign_pairwise c (k, k) (max s s')).forall
    ((idcAssign_prefix c (k, k) (le_max_left s s')).subset he)
    ((idcAssign_prefix c (k, k) (le_max_right s s')).subset he') hne'
  rcases hend with hA | hB
  · exact hsep.2.1 hA (by simp)
  · exact hsep.2.2 hB rfl
/-- Helper. -/
theorem idcMap_bound (D : Map) (c : Code) (mode b C : ℕ)
    (hb : ∀ x y, condK D x y ≤ condK (idcMap c mode) x y + (b : ℕ∞)) (hC : 3 + b ≤ C)
    {k l : ℕ} (hlk : l ≤ k) {out u v : BitString} (hmem : out ∈ idcFind c mode (k, l) (u, v)) :
    condK D out (pairCode u v) ≤ (logSlack C k : ℕ∞) := by
  have hprog : out ∈ idcMap c mode (pairCode (Nat.bits k) (Nat.bits l), pairCode u v) := by
    simpa [idcMap, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits] using hmem
  have hE : condK (idcMap c mode) out (pairCode u v) ≤
      ((pairCode (Nat.bits k) (Nat.bits l)).length : ℕ∞) :=
    (condK_le_iff _ _ _ _).2 ⟨_, le_rfl, hprog⟩
  have hbits := length_natBits_mono hlk
  have hlen := length_pairCode (Nat.bits k) (Nat.bits l)
  have hnat : (pairCode (Nat.bits k) (Nat.bits l)).length + b ≤ logSlack C k := by
    unfold logSlack
    nlinarith
  refine (hb _ _).trans ((add_le_add_left hE _).trans ?_)
  exact_mod_cast hnat
end PrefixColouring
end Kolmogorov
