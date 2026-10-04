/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Multisource.Requests

/-!
# Common information as an information transmission request

The common-information problem of SUV Chapter 11 — given `x`, `y` and `α, β, γ`, is there a
string `z` with `C(z) < α`, `C(x|z) < β` and `C(y|z) < γ`? — is, with logarithmic precision,
the request of Figure 47: the top node receives `x` and `y`, sends `z` down the middle channel
of capacity `α` and conditional descriptions down the side channels of capacities `β` and `γ`,
and the two output nodes must produce `x` and `y`.

Its cut-flow conditions `C(x) ≤ α + β`, `C(y) ≤ α + γ` and `C(x,y) ≤ α + β + γ` are the
instances of `condK_cutOutputs_le_cutCapacity` at the cuts of `commonInformationRequest_cuts`
(part of Problem 327); Chapter 11 shows that they are not sufficient.

Our requests give a node one input string, so the two inputs of the top node are given to it
as `listCode [x, y]`.

SUV Section 12.10, p. 388.
-/

namespace Kolmogorov

/-- The request of SUV Figure 47 on four nodes: `0` receives `x` and `y`, the middle channel
`0 → 1` has capacity `α`, the side channels `0 → 2` and `0 → 3` have capacities `β` and `γ`,
the relay `1` reaches both output nodes through unlimited channels, and `2` and `3` must
produce `x` and `y`.

SUV Figure 47, p. 389. -/
def commonInformationRequest (x y : BitString) (α β γ : ℕ) : InformationRequest (Fin 4) where
  edges := {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)}
  rank v := if v.val = 0 then 0 else if v.val = 1 then 1 else 2
  rank_lt := by decide +kernel
  capacity e :=
    if e = (0, 1) then (α : ℕ∞) else if e = (0, 2) then (β : ℕ∞)
    else if e = (0, 3) then (γ : ℕ∞) else ⊤
  input v := if v = 0 then some (listCode [x, y]) else none
  output v := if v = 2 then some x else if v = 3 then some y else none

/-- The three cuts of SUV Figure 47.  The cut `{1, 2}` (the relay and the output of `x`) is
entered by the channels of capacities `α` and `β`, the cut `{1, 3}` by those of capacities `α`
and `γ`, and the cut `{1, 2, 3}` by all three bounded channels; none of them contains an input,
and their outputs are `x`, `y` and `x, y`.  This gives the cut-flow conditions
`C(x) ≤ α + β`, `C(y) ≤ α + γ` and `C(x,y) ≤ α + β + γ`.

SUV Problem 327, p. 384 (conditions of p. 388). -/
theorem commonInformationRequest_cuts (x y : BitString) (α β γ : ℕ) :
    ((commonInformationRequest x y α β γ).cutCapacity {1, 2} = ((α + β : ℕ) : ℕ∞) ∧
      (commonInformationRequest x y α β γ).cutInputs {1, 2} = [] ∧
      (commonInformationRequest x y α β γ).cutOutputs {1, 2} = [x]) ∧
    ((commonInformationRequest x y α β γ).cutCapacity {1, 3} = ((α + γ : ℕ) : ℕ∞) ∧
      (commonInformationRequest x y α β γ).cutInputs {1, 3} = [] ∧
      (commonInformationRequest x y α β γ).cutOutputs {1, 3} = [y]) ∧
    ((commonInformationRequest x y α β γ).cutCapacity {1, 2, 3} = ((α + β + γ : ℕ) : ℕ∞) ∧
      (commonInformationRequest x y α β γ).cutInputs {1, 2, 3} = [] ∧
      (commonInformationRequest x y α β γ).cutOutputs {1, 2, 3} = [x, y]) := by
  have hcut12 :
      (commonInformationRequest x y α β γ).cutEdges {1, 2} = {(0, 1), (0, 2)} := by
    change (({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)} :
      Finset (Fin 4 × Fin 4)).filter fun e =>
        e.1 ∉ ({1, 2} : Finset (Fin 4)) ∧ e.2 ∈ ({1, 2} : Finset (Fin 4))) = _
    decide +kernel
  have hcut13 :
      (commonInformationRequest x y α β γ).cutEdges {1, 3} = {(0, 1), (0, 3)} := by
    change (({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)} :
      Finset (Fin 4 × Fin 4)).filter fun e =>
        e.1 ∉ ({1, 3} : Finset (Fin 4)) ∧ e.2 ∈ ({1, 3} : Finset (Fin 4))) = _
    decide +kernel
  have hcut123 :
      (commonInformationRequest x y α β γ).cutEdges {1, 2, 3} =
        {(0, 1), (0, 2), (0, 3)} := by
    change (({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)} :
      Finset (Fin 4 × Fin 4)).filter fun e =>
        e.1 ∉ ({1, 2, 3} : Finset (Fin 4)) ∧
          e.2 ∈ ({1, 2, 3} : Finset (Fin 4))) = _
    decide +kernel
  have hsort12 : ({1, 2} : Finset (Fin 4)).sort (· ≤ ·) = [1, 2] := by
    simpa using (List.toFinset_sort (r := (· ≤ ·)) (l := [1, 2]) (by simp)).2 (by simp)
  have hsort13 : ({1, 3} : Finset (Fin 4)).sort (· ≤ ·) = [1, 3] := by
    simpa using (List.toFinset_sort (r := (· ≤ ·)) (l := [1, 3]) (by simp)).2 (by simp)
  have hsort123 : ({1, 2, 3} : Finset (Fin 4)).sort (· ≤ ·) = [1, 2, 3] := by
    simpa using
      (List.toFinset_sort (r := (· ≤ ·)) (l := [1, 2, 3]) (by simp)).2 (by simp)
  simp only [InformationRequest.cutCapacity, hcut12, hcut13, hcut123,
    InformationRequest.cutInputs, InformationRequest.cutOutputs, hsort12, hsort13,
    hsort123]
  simp [commonInformationRequest, add_assoc]


private def M_decode (D : Map) (q : BitString × BitString) : Part BitString :=
  let p := q.1
  let z := q.2
  let code := decodeFirst p
  let side := decodeSecond p
  let p1 := (decodeListCode code).getD 0 []
  let p2 := (decodeListCode code).getD 1 []
  (D (p1, listCode [z])).bind fun relay =>
  D (p2, listCode [side, relay])

private lemma partrec_M (D : Map) (hD : isDecompressor D) : Partrec (M_decode D) := by
  let code : BitString × BitString → BitString := fun q => decodeFirst q.1
  let side : BitString × BitString → BitString := fun q => decodeSecond q.1
  let p1 : BitString × BitString → BitString := fun q => (decodeListCode (code q)).getD 0 []
  let p2 : BitString × BitString → BitString := fun q => (decodeListCode (code q)).getD 1 []
  have hcode : Computable code :=
    decodeFirst_computable.comp (f := decodeFirst) (g := Prod.fst) Computable.fst
  have hside : Computable side :=
    decodeSecond_computable.comp (f := decodeSecond) (g := Prod.fst) Computable.fst
  have hp1 : Computable p1 := (Primrec.list_getD []).to_comp.comp (f := _) (g := _)
    (decodeListCode_computable.comp (f := decodeListCode) (g := code) hcode) (Computable.const 0)
  have hp2 : Computable p2 := (Primrec.list_getD []).to_comp.comp (f := _) (g := _)
    (decodeListCode_computable.comp (f := decodeListCode) (g := code) hcode) (Computable.const 1)
  have hzlist : Computable (fun q : BitString × BitString => [q.2]) :=
    (Primrec.list_cons.comp (f := _) (g := _) Primrec.snd (Primrec.const [])).to_comp
  have hrelay : Partrec (fun q : BitString × BitString => D (p1 q, listCode [q.2])) :=
    hD.comp (f := D) (g := _) (hp1.pair (listCode_computable.comp (f := _) (g := _) hzlist))
  have h_inner : Partrec fun r : (BitString × BitString) × BitString =>
      D (p2 r.1, listCode [side r.1, r.2]) := by
    have h_p2 : Computable (fun r : (BitString × BitString) × BitString => p2 r.1) :=
      hp2.comp (f := p2) (g := Prod.fst) Computable.fst
    have h_side : Computable (fun r : (BitString × BitString) × BitString => side r.1) :=
      hside.comp (f := side) (g := Prod.fst) Computable.fst
    have h_relay : Computable (fun r : (BitString × BitString) × BitString => r.2) := Computable.snd
    have h_list : Computable (fun r : (BitString × BitString) × BitString => [side r.1, r.2]) :=
      (Primrec.list_cons.comp (f := _) (g := _) (Primrec.fst.comp (f := _) (g := _) Primrec.snd)
        (Primrec.list_cons.comp (f := _) (g := _) (Primrec.snd.comp (f := _) (g := _) Primrec.snd)
        (Primrec.const []))).to_comp.comp (f := _)
        (g := fun r : _ × BitString => (r, (side r.1, r.2)))
        (Computable.id.pair (h_side.pair h_relay))
    have h_listCode : Computable (fun r : (BitString × BitString) × BitString =>
        listCode [side r.1, r.2]) := listCode_computable.comp (f := listCode) (g := _) h_list
    exact hD.comp (f := D) (g := _) (h_p2.pair h_listCode)
  exact Partrec.bind (f := fun q => D (p1 q, listCode [q.2]))
    (g := fun q relay => D (p2 q, listCode [side q, relay])) hrelay h_inner


private lemma M_bound (D : Map) (hD : isOptimalConditional D) :
  ∃ cM : ℕ, ∀ (p w v : BitString), v ∈ M_decode D (p, w) → condK D v w ≤ (p.length : ℕ∞) + cM := by
    have h1 : Partrec (M_decode D) := partrec_M D hD.1
    obtain ⟨c, hc⟩ := hD.2 (M_decode D) h1
    refine ⟨c, fun p w v hv => (hc v w).trans ?_⟩
    gcongr
    exact sInf_le ⟨p, hv, rfl⟩


private lemma programLength_eq_length (p : BitString) : programLength p = p.length := rfl

/-- Two `O(log n)` conditional programs can be composed with `O(log n)` total cost, but their
constants need not be equal: the two program lengths add, together with self-delimiting
composition overhead.  Thus every fixed input constant is absorbed by a (possibly larger)
output constant, uniformly in the strings and capacity bound. -/
private theorem conditional_output_of_two_stage_messages (D : Map)
    (hD : isOptimalConditional D) :
    ∀ cIn : ℕ, ∃ cOut : ℕ, cIn ≤ cOut ∧
    ∀ (n k : ℕ) (x z side relay : BitString),
      x.length ≤ n → side.length ≤ k →
      condK D relay (listCode [z]) ≤ (logSlack cIn n : ℕ∞) →
      condK D x (listCode [side, relay]) ≤ (logSlack cIn n : ℕ∞) →
      condK D x z ≤ (k : ℕ∞) + (logSlack cOut n : ℕ∞) := by
  intro cIn
  obtain ⟨cM, hcM⟩ := M_bound D hD
  refine ⟨max cIn (8 * cIn + 6 + cM), le_max_left _ _,
    fun n k x z side relay hx hk hr hx_r => ?_⟩
  obtain ⟨p1, hp1_len, hp1_out⟩ := (condK_le_iff D relay (listCode [z]) (logSlack cIn n)).mp hr
  obtain ⟨p2, hp2_len, hp2_out⟩ :=
    (condK_le_iff D x (listCode [side, relay]) (logSlack cIn n)).mp hx_r
  let p := pairCode (listCode [p1, p2]) side
  have H1 : x ∈ M_decode D (p, z) := by
    unfold M_decode
    have H2 : decodeFirst p = listCode [p1, p2] := decodeFirst_pairCode _ _
    have H3 : decodeSecond p = side := decodeSecond_pairCode _ _
    simp only [H2, H3]
    have H4 : (decodeListCode (listCode [p1, p2])).getD 0 [] = p1 := by
      rw [decodeListCode_listCode]
      rfl
    have H5 : (decodeListCode (listCode [p1, p2])).getD 1 [] = p2 := by
      rw [decodeListCode_listCode]
      rfl
    simp only [H4, H5]
    exact Part.mem_bind_iff.mpr ⟨relay, hp1_out, hp2_out⟩
  have H2 : condK D x z ≤ (p.length : ℕ∞) + cM := hcM p z x H1
  have H3 : p.length = 4 * p1.length + 4 * p2.length + 5 + side.length := by
    change (pairCode (listCode [p1, p2]) side).length = _
    rw [length_pairCode, length_listCode_cons, length_listCode_cons]
    simp only [listCode_nil, List.length_nil, add_zero]
    omega
  have Hp1_len : p1.length ≤ logSlack cIn n := by
    have h : p1.length = programLength p1 := rfl
    exact h ▸ hp1_len
  have Hp2_len : p2.length ≤ logSlack cIn n := by
    have h : p2.length = programLength p2 := rfl
    exact h ▸ hp2_len
  refine H2.trans ?_
  calc
    (p.length : ℕ∞) + cM ≤ ((8 * logSlack cIn n + 6 + k : ℕ) : ℕ∞) + cM := by
      gcongr
      have h1 : side.length ≤ k := hk
      have h2 : p1.length ≤ logSlack cIn n := Hp1_len
      have h3 : p2.length ≤ logSlack cIn n := Hp2_len
      omega
    _ = (k : ℕ∞) + ((8 * logSlack cIn n + 6 + cM : ℕ) : ℕ∞) := by
      push_cast
      have h4 : (8 * logSlack cIn n + 6 + k : ℕ) + cM =
        k + (8 * logSlack cIn n + 6 + cM) := by omega
      exact_mod_cast congrArg Nat.cast h4
    _ ≤ (k : ℕ∞) + (logSlack (max cIn (8 * cIn + 6 + cM)) n : ℕ∞) := by
      gcongr
      unfold logSlack
      have h1 : 8 * (cIn * n.bits.length + cIn) + 6 + cM =
        8 * cIn * n.bits.length + 8 * cIn + 6 + cM := by ring
      rw [h1]
      have h6 : 8 * cIn + 6 + cM ≤ max cIn (8 * cIn + 6 + cM) := le_max_right _ _
      have h7 : 8 * cIn * (n.bits.length) ≤
          max cIn (8 * cIn + 6 + cM) * (n.bits.length) := by
        have h8 : 8 * cIn ≤ max cIn (8 * cIn + 6 + cM) := by
          have h9 : 8 * cIn ≤ 8 * cIn + 6 + cM := by omega
          exact h9.trans (le_max_right _ _)
        exact Nat.mul_le_mul_right _ h8
      omega

private theorem commonInformationRequest_local_conditions (D : Map) (x y : BitString)
    (α β γ ε : ℕ) (t : Fin 4 × Fin 4 → BitString)
    (hful : IsFulfilled D (commonInformationRequest x y α β γ) t ε) :
    (t (0, 1)).length ≤ α ∧ (t (0, 2)).length ≤ β ∧ (t (0, 3)).length ≤ γ ∧
      condK D (t (1, 2)) (listCode [t (0, 1)]) ≤ (ε : ℕ∞) ∧
      condK D (t (1, 3)) (listCode [t (0, 1)]) ≤ (ε : ℕ∞) ∧
      condK D x (listCode [t (0, 2), t (1, 2)]) ≤ (ε : ℕ∞) ∧
      condK D y (listCode [t (0, 3), t (1, 3)]) ≤ (ε : ℕ∞) := by
  have hlen01 := hful.1 (0, 1) (by simp [commonInformationRequest])
  have hlen02 := hful.1 (0, 2) (by simp [commonInformationRequest])
  have hlen03 := hful.1 (0, 3) (by simp [commonInformationRequest])
  change ((t (0, 1)).length : ℕ∞) ≤ (α : ℕ∞) at hlen01
  change ((t (0, 2)).length : ℕ∞) ≤ (β : ℕ∞) at hlen02
  change ((t (0, 3)).length : ℕ∞) ≤ (γ : ℕ∞) at hlen03
  have hin1 :
      (commonInformationRequest x y α β γ).inNeighbors 1 = {0} := by
    change (Finset.image Prod.fst
      (({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)} : Finset (Fin 4 × Fin 4)).filter
        fun e => e.2 = 1)) = _
    decide +kernel
  have hin2 :
      (commonInformationRequest x y α β γ).inNeighbors 2 = {0, 1} := by
    change (Finset.image Prod.fst
      (({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)} : Finset (Fin 4 × Fin 4)).filter
        fun e => e.2 = 2)) = _
    decide +kernel
  have hin3 :
      (commonInformationRequest x y α β γ).inNeighbors 3 = {0, 1} := by
    change (Finset.image Prod.fst
      (({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)} : Finset (Fin 4 × Fin 4)).filter
        fun e => e.2 = 3)) = _
    decide +kernel
  have hsort1 : ({0} : Finset (Fin 4)).sort (· ≤ ·) = [0] := by
    decide +kernel
  have hsort01 : ({0, 1} : Finset (Fin 4)).sort (· ≤ ·) = [0, 1] := by
    simpa using
      (List.toFinset_sort (r := (· ≤ ·)) (l := [0, 1]) (by simp)).2 (by simp)
  have hrelay12 := hful.2 1 (t (1, 2)) (by
    simp [InformationRequest.outgoing, InformationRequest.outNeighbors,
      commonInformationRequest])
  have hrelay13 := hful.2 1 (t (1, 3)) (by
    simp [InformationRequest.outgoing, InformationRequest.outNeighbors,
      commonInformationRequest])
  have hout2 := hful.2 2 x (by
    simp [InformationRequest.outgoing, InformationRequest.outNeighbors,
      commonInformationRequest])
  have hout3 := hful.2 3 y (by
    simp [InformationRequest.outgoing, InformationRequest.outNeighbors,
      commonInformationRequest])
  rw [InformationRequest.incoming, hin1, hsort1] at hrelay12 hrelay13
  rw [InformationRequest.incoming, hin2, hsort01] at hout2
  rw [InformationRequest.incoming, hin3, hsort01] at hout3
  exact ⟨by exact_mod_cast hlen01, by exact_mod_cast hlen02, by exact_mod_cast hlen03,
    hrelay12, hrelay13, hout2, hout3⟩

/-- Fulfilling the request of Figure 47 produces common information: the string sent down the
middle channel has complexity at most `α` and makes `x` and `y` conditionally simple within
`β` and `γ`, all up to `O(log n)`.  The premise and conclusion use independent hidden
constants because composing the two local decoding stages adds their logarithmic losses; the
book states only logarithmic precision, not equality of those constants (SUV p. 388).

SUV Section 12.10, p. 388 (unnumbered claim). -/
theorem exists_commonInformation_of_fulfilled (D : Map) (hD : isOptimalConditional D) :
    ∀ c₁ : ℕ, ∃ c₂ : ℕ, ∀ (n α β γ : ℕ) (x y : BitString)
      (t : Fin 4 × Fin 4 → BitString),
      x.length ≤ n → y.length ≤ n →
      IsFulfilled D (commonInformationRequest x y α β γ) t (logSlack c₁ n) →
      ∃ z : BitString, plainK D z ≤ (α : ℕ∞) + (logSlack c₂ n : ℕ∞) ∧
        condK D x z ≤ (β : ℕ∞) + (logSlack c₂ n : ℕ∞) ∧
        condK D y z ≤ (γ : ℕ∞) + (logSlack c₂ n : ℕ∞) := by
  intro c₁
  obtain ⟨c₀, hc₀⟩ := plainK_le_length D hD
  obtain ⟨c₂, hc₁c₂, hc⟩ := conditional_output_of_two_stage_messages D hD c₁
  refine ⟨c₂ + c₀, fun n α β γ x y t hx hy hful => ?_⟩
  obtain ⟨hz, hsx, hsy, hrx, hry, houtx, houty⟩ :=
    commonInformationRequest_local_conditions D x y α β γ (logSlack c₁ n) t hful
  have hplain : plainK D (t (0, 1)) ≤
      (α : ℕ∞) + (logSlack (c₂ + c₀) n : ℕ∞) := by
    calc
      plainK D (t (0, 1)) ≤ ((t (0, 1)).length : ℕ∞) + (c₀ : ℕ∞) := hc₀ _
      _ ≤ (α : ℕ∞) + (logSlack (c₂ + c₀) n : ℕ∞) := by
        norm_cast
        simp only [logSlack]
        omega
  refine ⟨t (0, 1), hplain, ?_, ?_⟩
  · exact (hc n β x (t (0, 1)) (t (0, 2)) (t (1, 2)) hx hsx hrx houtx).trans
      (by gcongr; exact_mod_cast logSlack_mono_left (Nat.le_add_right c₂ c₀) n)
  · exact (hc n γ y (t (0, 1)) (t (0, 3)) (t (1, 3)) hy hsy hry houty).trans
      (by gcongr; exact_mod_cast logSlack_mono_left (Nat.le_add_right c₂ c₀) n)

/-- Selection from the domain of a partial computable relation: a partial computable `f`
picks, for every `a`, some `b` with `g (a, b)` defined, whenever there is one. -/
private theorem partrec_domain_selector {α β : Type*} [Primcodable α] [Primcodable β]
    (g : α × β →. Unit) (hg : Partrec g) :
    ∃ f : α →. β, Partrec f ∧ (∀ a b, b ∈ f a → (g (a, b)).Dom) ∧
      ∀ a b, (g (a, b)).Dom → (f a).Dom := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg
  let check : α → ℕ → Option β := fun a n =>
    (Encodable.decode (α := β) n.unpair.1).bind fun b =>
      bif (Nat.Partrec.Code.evaln n.unpair.2 c (Encodable.encode (a, b))).isSome
      then some b else none
  have hcheck : Computable₂ check := by
    have hstep : Primrec₂ fun (q : α × ℕ) (b : β) =>
        bif (Nat.Partrec.Code.evaln q.2.unpair.2 c (Encodable.encode (q.1, b))).isSome
        then some b else none := by
      refine Primrec.cond ?_ (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
      have he : Primrec fun q : (α × ℕ) × β =>
          ((q.1.2.unpair.2, c), Encodable.encode (q.1.1, q.2)) :=
        Primrec.pair (Primrec.pair
          (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.const c))
          (Primrec.encode.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
      exact Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp he)
    have h : Primrec₂ check :=
      Primrec.option_bind
        (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))) hstep
    exact h.to_comp
  have hdom : ∀ a b, (g (a, b)).Dom ↔
      ∃ k, (Nat.Partrec.Code.evaln k c (Encodable.encode (a, b))).isSome := by
    intro a b
    have h1 : c.eval (Encodable.encode (a, b)) = (g (a, b)).map Encodable.encode := by
      rw [hc]; simp
    constructor
    · intro h
      obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp
        (show Encodable.encode ((g (a, b)).get h) ∈ c.eval (Encodable.encode (a, b)) by
          rw [h1]; exact Part.mem_map _ (Part.get_mem h))
      exact ⟨k, Option.isSome_iff_exists.mpr ⟨_, hk⟩⟩
    · rintro ⟨k, hk⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
      have := Nat.Partrec.Code.evaln_sound hv
      rw [h1] at this
      exact (Part.dom_iff_mem.mpr ⟨v, this⟩ : ((g (a, b)).map Encodable.encode).Dom)
  refine ⟨fun a => Nat.rfindOpt (check a), Partrec.rfindOpt hcheck, ?_, ?_⟩
  · intro a b hb
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hb
    simp only [check, Option.mem_def, Option.bind_eq_some_iff] at hn
    obtain ⟨b', -, hb'⟩ := hn
    cases hs : (Nat.Partrec.Code.evaln n.unpair.2 c (Encodable.encode (a, b'))).isSome
    · rw [hs] at hb'
      simp at hb'
    · rw [hs] at hb'
      simp only [Bool.cond_true, Option.some.injEq] at hb'
      subst hb'
      exact (hdom a b').mpr ⟨_, hs⟩
  · intro a b hab
    obtain ⟨k, hk⟩ := (hdom a b).mp hab
    refine Nat.rfindOpt_dom.mpr ⟨Nat.pair (Encodable.encode b) k, b, ?_⟩
    simp only [check, Nat.unpair_pair, Encodable.encodek, Option.bind_some, hk, Bool.cond_true]
    rfl


/-- The search of the top node of Figure 47 is partial computable: given bounds `a, b, g` and
`x, y`, it finds programs `p, qx, qy` of lengths at most `a, b, g` with `p` producing some `z`
from which `qx` and `qy` produce `x` and `y`, whenever such programs exist. -/
private theorem exists_commonDescription_search (D : Map) (hD : isDecompressor D) :
    ∃ f : (ℕ × ℕ × ℕ) × BitString × BitString →. BitString × BitString × BitString,
      Partrec f ∧
      (∀ a b g x y p qx qy, (p, qx, qy) ∈ f ((a, b, g), x, y) →
        ∃ z, z ∈ D (p, []) ∧ x ∈ D (qx, z) ∧ y ∈ D (qy, z) ∧
          p.length ≤ a ∧ qx.length ≤ b ∧ qy.length ≤ g) ∧
      (∀ a b g x y p qx qy z, z ∈ D (p, []) → x ∈ D (qx, z) → y ∈ D (qy, z) →
        p.length ≤ a → qx.length ≤ b → qy.length ≤ g → (f ((a, b, g), x, y)).Dom) := by
  let Q := ((ℕ × ℕ × ℕ) × BitString × BitString) × (BitString × BitString × BitString)
  let ok : Q → BitString → BitString → Prop := fun q x' y' =>
    x' = q.1.2.1 ∧ y' = q.1.2.2 ∧ q.2.1.length ≤ q.1.1.1 ∧
      q.2.2.1.length ≤ q.1.1.2.1 ∧ q.2.2.2.length ≤ q.1.1.2.2
  let g : Q →. Unit := fun q => (D (q.2.1, [])).bind fun z => (D (q.2.2.1, z)).bind fun x' =>
    (D (q.2.2.2, z)).bind fun y' => Part.ofOption (if ok q x' y' then some () else none)
  have hg : Partrec g := by
    have hlast : Primrec fun r : ((Q × BitString) × BitString) × BitString =>
        if ok r.1.1.1 r.1.2 r.2 then some () else none := by
      have hq : Primrec fun r : ((Q × BitString) × BitString) × BitString => r.1.1.1 :=
        Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
      refine Primrec.ite ?_ (Primrec.const _) (Primrec.const _)
      refine PrimrecPred.and (Primrec.eq.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp hq)))) ?_
      refine PrimrecPred.and (Primrec.eq.comp Primrec.snd
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp hq)))) ?_
      refine PrimrecPred.and (Primrec.nat_le.comp
        (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp hq)))
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp hq)))) ?_
      refine PrimrecPred.and (Primrec.nat_le.comp
        (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hq))))
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp hq))))) ?_
      exact Primrec.nat_le.comp
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hq))))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp hq))))
    have h3 : Partrec fun r : (Q × BitString) × BitString =>
        (D (r.1.1.2.2.2, r.1.2)).bind fun y' =>
          Part.ofOption (if ok r.1.1 r.2 y' then some () else none) :=
      Partrec.bind (hD.comp (Computable.pair
          (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
            (Computable.fst.comp Computable.fst))))
          (Computable.snd.comp Computable.fst)))
        (Computable.ofOption hlast.to_comp).to₂
    have h2 : Partrec fun r : Q × BitString =>
        (D (r.1.2.2.1, r.2)).bind fun x' => (D (r.1.2.2.2, r.2)).bind fun y' =>
          Part.ofOption (if ok r.1 x' y' then some () else none) :=
      Partrec.bind (hD.comp (Computable.pair
          (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
          Computable.snd)) h3.to₂
    exact Partrec.bind (hD.comp (Computable.pair (Computable.fst.comp Computable.snd)
      (Computable.const []))) h2.to₂
  have hgdom : ∀ q : Q, (g q).Dom ↔ ∃ z, z ∈ D (q.2.1, []) ∧ q.1.2.1 ∈ D (q.2.2.1, z) ∧
      q.1.2.2 ∈ D (q.2.2.2, z) ∧ q.2.1.length ≤ q.1.1.1 ∧
      q.2.2.1.length ≤ q.1.1.2.1 ∧ q.2.2.2.length ≤ q.1.1.2.2 := by
    intro q
    simp only [g, Part.dom_iff_mem, Part.mem_bind_iff]
    constructor
    · rintro ⟨u, z, hz, x', hx', y', hy', hu⟩
      by_cases hok : ok q x' y'
      · obtain ⟨rfl, rfl, h1, h2, h3⟩ := hok
        exact ⟨z, hz, hx', hy', h1, h2, h3⟩
      · rw [ite_eq_right hok] at hu
        exact absurd hu (by simp)
    · rintro ⟨z, hz, hx, hy, h1, h2, h3⟩
      have hok : ok q q.1.2.1 q.1.2.2 := ⟨rfl, rfl, h1, h2, h3⟩
      refine ⟨(), z, hz, _, hx, _, hy, ?_⟩
      rw [ite_eq_left hok]
      exact Part.mem_some _
  obtain ⟨f, hf, hfsound, hfdom⟩ := partrec_domain_selector g hg
  refine ⟨f, hf, fun a b g' x y p qx qy hmem => ?_,
    fun a b g' x y p qx qy z hz hx hy h1 h2 h3 => ?_⟩
  · exact (hgdom (((a, b, g'), x, y), (p, qx, qy))).mp (hfsound _ _ hmem)
  · exact hfdom _ (p, qx, qy)
      ((hgdom (((a, b, g'), x, y), (p, qx, qy))).mpr ⟨z, hz, hx, hy, h1, h2, h3⟩)


/-- An output of a partial computable map costs at most the length of its program. -/
private theorem condK_le_length_add_of_partrec (D : Map) (hD : isOptimalConditional D)
    (M : Map) (hM : Partrec M) :
    ∃ c : ℕ, ∀ p w v, v ∈ M (p, w) → condK D v w ≤ (p.length : ℕ∞) + c := by
  obtain ⟨c, hc⟩ := hD.2 M hM
  refine ⟨c, fun p w v hv => (hc v w).trans ?_⟩
  gcongr
  exact sInf_le ⟨p, hv, rfl⟩

/-- Common descriptions found by search: given `x, y` and the advice `a, b, g`, the programs
found by the search have conditional complexity at most the length of the advice. -/
private theorem exists_searched_commonDescription (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (a b g : ℕ) (x y p₀ qx₀ qy₀ z₀ : BitString),
      z₀ ∈ D (p₀, []) → x ∈ D (qx₀, z₀) → y ∈ D (qy₀, z₀) →
      p₀.length ≤ a → qx₀.length ≤ b → qy₀.length ≤ g →
      ∃ p qx qy z : BitString, z ∈ D (p, []) ∧ x ∈ D (qx, z) ∧ y ∈ D (qy, z) ∧
        p.length ≤ a ∧ qx.length ≤ b ∧ qy.length ≤ g ∧
        condK D p (listCode [listCode [x, y]]) ≤
          ((listCode [Nat.bits a, Nat.bits b, Nat.bits g]).length : ℕ∞) + c ∧
        condK D qx (listCode [listCode [x, y]]) ≤
          ((listCode [Nat.bits a, Nat.bits b, Nat.bits g]).length : ℕ∞) + c ∧
        condK D qy (listCode [listCode [x, y]]) ≤
          ((listCode [Nat.bits a, Nat.bits b, Nat.bits g]).length : ℕ∞) + c := by
  obtain ⟨f, hf, hsound, hdom⟩ := exists_commonDescription_search D hD.1
  let dec : BitString × BitString → (ℕ × ℕ × ℕ) × BitString × BitString := fun q =>
    ((decodeBits ((decodeListCode q.1).getD 0 []), decodeBits ((decodeListCode q.1).getD 1 []),
        decodeBits ((decodeListCode q.1).getD 2 [])),
      (decodeListCode ((decodeListCode q.2).getD 0 [])).getD 0 [],
      (decodeListCode ((decodeListCode q.2).getD 0 [])).getD 1 [])
  have hdec : Computable dec := by
    have hl : Primrec fun q : BitString × BitString => decodeListCode q.1 :=
      decodeListCode_primrec.comp Primrec.fst
    have hu : Primrec fun q : BitString × BitString =>
        decodeListCode ((decodeListCode q.2).getD 0 []) :=
      decodeListCode_primrec.comp ((Primrec.list_getD []).comp
        (decodeListCode_primrec.comp Primrec.snd) (Primrec.const 0))
    have hget : ∀ i : ℕ, Primrec fun q : BitString × BitString =>
        decodeBits ((decodeListCode q.1).getD i []) := fun i =>
      primrec_decodeBits.comp ((Primrec.list_getD []).comp hl (Primrec.const i))
    exact (Primrec.pair (Primrec.pair (hget 0) (Primrec.pair (hget 1) (hget 2)))
      (Primrec.pair ((Primrec.list_getD []).comp hu (Primrec.const 0))
        ((Primrec.list_getD []).comp hu (Primrec.const 1)))).to_comp
  have hdec_eq : ∀ (a b g : ℕ) (x y : BitString),
      dec (listCode [Nat.bits a, Nat.bits b, Nat.bits g], listCode [listCode [x, y]]) =
        ((a, b, g), x, y) := by
    intro a b g x y
    simp only [dec, decodeListCode_listCode, List.getD_cons_zero, List.getD_cons_succ,
      decodeBits_natBits]
  obtain ⟨c₁, hc₁⟩ := condK_le_length_add_of_partrec D hD
    (fun q => (f (dec q)).map Prod.fst)
    ((hf.comp hdec).map (Computable.fst.comp Computable.snd).to₂)
  obtain ⟨c₂, hc₂⟩ := condK_le_length_add_of_partrec D hD
    (fun q => (f (dec q)).map fun r => r.2.1)
    ((hf.comp hdec).map (Computable.fst.comp (Computable.snd.comp Computable.snd)).to₂)
  obtain ⟨c₃, hc₃⟩ := condK_le_length_add_of_partrec D hD
    (fun q => (f (dec q)).map fun r => r.2.2)
    ((hf.comp hdec).map (Computable.snd.comp (Computable.snd.comp Computable.snd)).to₂)
  refine ⟨c₁ + c₂ + c₃, fun a b g x y p₀ qx₀ qy₀ z₀ hz₀ hx₀ hy₀ h₁ h₂ h₃ => ?_⟩
  have hD' := hdom a b g x y p₀ qx₀ qy₀ z₀ hz₀ hx₀ hy₀ h₁ h₂ h₃
  have hr := Part.get_mem hD'
  set r := (f ((a, b, g), x, y)).get hD'
  obtain ⟨z, hz, hx, hy, hl₁, hl₂, hl₃⟩ := hsound a b g x y r.1 r.2.1 r.2.2 hr
  have hmem : r ∈ f (dec (listCode [Nat.bits a, Nat.bits b, Nat.bits g],
      listCode [listCode [x, y]])) := by
    rw [hdec_eq]; exact hr
  refine ⟨r.1, r.2.1, r.2.2, z, hz, hx, hy, hl₁, hl₂, hl₃, ?_, ?_, ?_⟩
  · refine (hc₁ _ _ _ (Part.mem_map _ hmem)).trans ?_
    gcongr; omega
  · refine (hc₂ _ _ _ (Part.mem_map _ hmem)).trans ?_
    gcongr; omega
  · refine (hc₃ _ _ _ (Part.mem_map _ hmem)).trans ?_
    gcongr; omega


/-- The relay recovers `z` from its program, and the output nodes recover `x` from a
conditional program and `z`, at constant cost. -/
private theorem exists_commonDescription_decoders (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, (∀ p z, z ∈ D (p, []) → condK D z (listCode [p]) ≤ (c : ℕ∞)) ∧
      ∀ q z v, v ∈ D (q, z) → condK D v (listCode [q, z]) ≤ (c : ℕ∞) := by
  have hl : Computable fun q : BitString × BitString => decodeListCode q.2 :=
    decodeListCode_computable.comp Computable.snd
  have hget : ∀ i : ℕ, Computable fun q : BitString × BitString =>
      (decodeListCode q.2).getD i [] := fun i =>
    (Primrec.list_getD []).to_comp.comp hl (Computable.const i)
  obtain ⟨c₁, hc₁⟩ := condK_le_length_add_of_partrec D hD
    (fun q => D ((decodeListCode q.2).getD 0 [], []))
    (hD.1.comp ((hget 0).pair (Computable.const [])))
  obtain ⟨c₂, hc₂⟩ := condK_le_length_add_of_partrec D hD
    (fun q => D ((decodeListCode q.2).getD 0 [], (decodeListCode q.2).getD 1 []))
    (hD.1.comp ((hget 0).pair (hget 1)))
  refine ⟨c₁ + c₂, fun p z hz => ?_, fun q z v hv => ?_⟩
  · refine (hc₁ [] (listCode [p]) z ?_).trans ?_
    · simp only [decodeListCode_listCode, List.getD_cons_zero]; exact hz
    · simp only [List.length_nil, Nat.cast_zero, zero_add]; gcongr; omega
  · refine (hc₂ [] (listCode [q, z]) v ?_).trans ?_
    · simp only [decodeListCode_listCode, List.getD_cons_zero]; exact hv
    · simp only [List.length_nil, Nat.cast_zero, zero_add]; gcongr; omega

/-- When the middle channel can carry the whole pair `listCode [x, y]`, all messages are
simple functions of the node inputs. -/
private theorem exists_trivial_commonDescription_decoders (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ x y : BitString,
      condK D (listCode [x, y]) (listCode [listCode [x, y]]) ≤ (c : ℕ∞) ∧
      condK D [] (listCode [listCode [x, y]]) ≤ (c : ℕ∞) ∧
      condK D x (listCode [listCode [x, y]]) ≤ (c : ℕ∞) ∧
      condK D y (listCode [listCode [x, y]]) ≤ (c : ℕ∞) ∧
      condK D x (listCode [[], x]) ≤ (c : ℕ∞) ∧ condK D y (listCode [[], y]) ≤ (c : ℕ∞) := by
  have hget : ∀ i : ℕ, Computable fun w : BitString => (decodeListCode w).getD i [] :=
    fun i => (Primrec.list_getD []).to_comp.comp decodeListCode_computable (Computable.const i)
  obtain ⟨c₁, hc₁⟩ := condK_comp D hD _ (hget 0)
  obtain ⟨c₂, hc₂⟩ := condK_comp D hD _ (Computable.const ([] : BitString))
  obtain ⟨c₃, hc₃⟩ := condK_comp D hD _ ((hget 0).comp (hget 0))
  obtain ⟨c₄, hc₄⟩ := condK_comp D hD _ ((hget 1).comp (hget 0))
  obtain ⟨c₅, hc₅⟩ := condK_comp D hD _ (hget 1)
  have hle : ∀ {a : ℕ∞} {i : ℕ}, i ≤ c₁ + c₂ + c₃ + c₄ + c₅ → a ≤ (i : ℕ∞) →
      a ≤ ((c₁ + c₂ + c₃ + c₄ + c₅ : ℕ) : ℕ∞) := fun hi ha => ha.trans (by exact_mod_cast hi)
  refine ⟨c₁ + c₂ + c₃ + c₄ + c₅, fun x y => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have h := hc₁ (listCode [listCode [x, y]])
    simp only [decodeListCode_listCode, List.getD_cons_zero] at h
    exact hle (i := c₁) (by omega) h
  · exact hle (i := c₂) (by omega) (hc₂ (listCode [listCode [x, y]]))
  · have h := hc₃ (listCode [listCode [x, y]])
    simp only [decodeListCode_listCode, List.getD_cons_zero] at h
    exact hle (i := c₃) (by omega) h
  · have h := hc₄ (listCode [listCode [x, y]])
    simp only [decodeListCode_listCode, List.getD_cons_zero] at h
    exact hle (i := c₄) (by omega) h
  · have h := hc₅ (listCode [[], x])
    simp only [decodeListCode_listCode] at h
    exact hle (i := c₅) (by omega) h
  · have h := hc₅ (listCode [[], y])
    simp only [decodeListCode_listCode] at h
    exact hle (i := c₅) (by omega) h

/-- Numbers linear in `n` have binary length logarithmic in `n`. -/
private theorem length_bits_le_of_le_four_mul_add (n k m : ℕ) (h : m ≤ 4 * n + k) :
    (Nat.bits m).length ≤ 4 * (Nat.bits n).length + 4 + k := by
  have h1 := length_natBits_mono h
  have h2 := length_natBits_add_le (n + n + (n + n)) k
  have h3 := length_natBits_add_le (n + n) (n + n)
  have h4 := length_natBits_add_le n n
  have h5 := length_natBits_le k
  have h6 : 4 * n + k = n + n + (n + n) + k := by ring
  rw [h6] at h1
  omega

/-- Converse of `commonInformationRequest_local_conditions`: the edge-length bounds and the
seven local conditions at the four nodes give a fulfilment of Figure 47. -/
private theorem commonInformationRequest_fulfilled_of_local (D : Map) (x y : BitString)
    (α β γ ε : ℕ) (t : Fin 4 × Fin 4 → BitString)
    (hl01 : (t (0, 1)).length ≤ α) (hl02 : (t (0, 2)).length ≤ β)
    (hl03 : (t (0, 3)).length ≤ γ)
    (h01 : condK D (t (0, 1)) (listCode [listCode [x, y]]) ≤ (ε : ℕ∞))
    (h02 : condK D (t (0, 2)) (listCode [listCode [x, y]]) ≤ (ε : ℕ∞))
    (h03 : condK D (t (0, 3)) (listCode [listCode [x, y]]) ≤ (ε : ℕ∞))
    (h12 : condK D (t (1, 2)) (listCode [t (0, 1)]) ≤ (ε : ℕ∞))
    (h13 : condK D (t (1, 3)) (listCode [t (0, 1)]) ≤ (ε : ℕ∞))
    (h2 : condK D x (listCode [t (0, 2), t (1, 2)]) ≤ (ε : ℕ∞))
    (h3 : condK D y (listCode [t (0, 3), t (1, 3)]) ≤ (ε : ℕ∞)) :
    IsFulfilled D (commonInformationRequest x y α β γ) t ε := by
  have hin0 : (commonInformationRequest x y α β γ).inNeighbors 0 = ∅ := by
    change (Finset.image Prod.fst
      (({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)} : Finset (Fin 4 × Fin 4)).filter
        fun e => e.2 = 0)) = _
    decide +kernel
  have hin1 : (commonInformationRequest x y α β γ).inNeighbors 1 = {0} := by
    change (Finset.image Prod.fst
      (({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)} : Finset (Fin 4 × Fin 4)).filter
        fun e => e.2 = 1)) = _
    decide +kernel
  have hin2 : (commonInformationRequest x y α β γ).inNeighbors 2 = {0, 1} := by
    change (Finset.image Prod.fst
      (({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)} : Finset (Fin 4 × Fin 4)).filter
        fun e => e.2 = 2)) = _
    decide +kernel
  have hin3 : (commonInformationRequest x y α β γ).inNeighbors 3 = {0, 1} := by
    change (Finset.image Prod.fst
      (({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)} : Finset (Fin 4 × Fin 4)).filter
        fun e => e.2 = 3)) = _
    decide +kernel
  have hout0 : (commonInformationRequest x y α β γ).outNeighbors 0 = {1, 2, 3} := by
    change (Finset.image Prod.snd
      (({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)} : Finset (Fin 4 × Fin 4)).filter
        fun e => e.1 = 0)) = _
    decide +kernel
  have hout1 : (commonInformationRequest x y α β γ).outNeighbors 1 = {2, 3} := by
    change (Finset.image Prod.snd
      (({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)} : Finset (Fin 4 × Fin 4)).filter
        fun e => e.1 = 1)) = _
    decide +kernel
  have hout2 : (commonInformationRequest x y α β γ).outNeighbors 2 = ∅ := by
    change (Finset.image Prod.snd
      (({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)} : Finset (Fin 4 × Fin 4)).filter
        fun e => e.1 = 2)) = _
    decide +kernel
  have hout3 : (commonInformationRequest x y α β γ).outNeighbors 3 = ∅ := by
    change (Finset.image Prod.snd
      (({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)} : Finset (Fin 4 × Fin 4)).filter
        fun e => e.1 = 3)) = _
    decide +kernel
  have hsort0 : ({0} : Finset (Fin 4)).sort (· ≤ ·) = [0] := by
    decide +kernel
  have hsort01 : ({0, 1} : Finset (Fin 4)).sort (· ≤ ·) = [0, 1] := by
    simpa using
      (List.toFinset_sort (r := (· ≤ ·)) (l := [0, 1]) (by simp)).2 (by simp)
  have hsort23 : ({2, 3} : Finset (Fin 4)).sort (· ≤ ·) = [2, 3] := by
    simpa using
      (List.toFinset_sort (r := (· ≤ ·)) (l := [2, 3]) (by simp)).2 (by simp)
  have hsort123 : ({1, 2, 3} : Finset (Fin 4)).sort (· ≤ ·) = [1, 2, 3] := by
    simpa using
      (List.toFinset_sort (r := (· ≤ ·)) (l := [1, 2, 3]) (by simp)).2 (by simp)
  refine ⟨fun e he => ?_, fun v s hs => ?_⟩
  · simp only [commonInformationRequest, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
      simp only [Fin.isValue, commonInformationRequest, Fin.val_eq_zero_iff, listCode_cons,
        listCode_nil, Prod.mk.injEq, one_ne_zero, Fin.reduceEq, and_false, and_self,
        ↓reduceIte, and_true, Nat.cast_zero, add_zero, Nat.cast_le, le_top] <;> assumption
  · have hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
      clear hs; revert v; decide
    rcases hv with rfl | rfl | rfl | rfl
    · simp only [InformationRequest.outgoing, hout0, hsort123] at hs
      simp only [InformationRequest.incoming, hin0]
      simp only [Fin.isValue, List.map_cons, List.map_nil, commonInformationRequest,
        Fin.val_eq_zero_iff, listCode_cons, listCode_nil, Fin.reduceEq, ↓reduceIte,
        Option.toList_none, List.append_nil, List.mem_cons, List.not_mem_nil, or_false,
        Finset.sort_empty, Option.toList_some, List.nil_append, ge_iff_le] at hs ⊢
      rcases hs with rfl | rfl | rfl <;> assumption
    · simp only [InformationRequest.outgoing, hout1, hsort23] at hs
      simp only [InformationRequest.incoming, hin1, hsort0]
      simp only [Fin.isValue, List.map_cons, List.map_nil, commonInformationRequest,
        Fin.val_eq_zero_iff, listCode_cons, listCode_nil, Fin.reduceEq, ↓reduceIte,
        Option.toList_none, List.append_nil, List.mem_cons, List.not_mem_nil, or_false,
        one_ne_zero, ge_iff_le] at hs ⊢
      rcases hs with rfl | rfl <;> assumption
    · simp only [InformationRequest.outgoing, hout2] at hs
      simp only [InformationRequest.incoming, hin2, hsort01]
      simp only [Fin.isValue, Finset.sort_empty, List.map_nil, commonInformationRequest,
        Fin.val_eq_zero_iff, listCode_cons, listCode_nil, ↓reduceIte, Option.toList_some,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.map_cons,
        Fin.reduceEq, Option.toList_none, List.append_nil, ge_iff_le] at hs ⊢
      subst hs; assumption
    · simp only [InformationRequest.outgoing, hout3] at hs
      simp only [InformationRequest.incoming, hin3, hsort01]
      simp only [Fin.isValue, Finset.sort_empty, List.map_nil, commonInformationRequest,
        Fin.val_eq_zero_iff, listCode_cons, listCode_nil, Fin.reduceEq, ↓reduceIte,
        Option.toList_some, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
        List.map_cons, Option.toList_none, List.append_nil, ge_iff_le] at hs ⊢
      subst hs; assumption

/-- Conversely, common information fulfils the request of Figure 47: the witness `z` is sent
down the middle channel and the conditional descriptions down the side channels, all of them
found by search with logarithmic advice from `x` and `y`.

SUV Section 12.10, p. 388 (unnumbered claim). -/
theorem exists_fulfilled_of_commonInformation (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (n α β γ : ℕ) (x y z : BitString),
      x.length ≤ n → y.length ≤ n →
      plainK D z ≤ (α : ℕ∞) → condK D x z ≤ (β : ℕ∞) → condK D y z ≤ (γ : ℕ∞) →
      ∃ t : Fin 4 × Fin 4 → BitString,
        IsFulfilled D (commonInformationRequest x y α β γ) t (logSlack c n) := by
  obtain ⟨cS, hS⟩ := exists_searched_commonDescription D hD
  obtain ⟨cR, hR₁, hR₂⟩ := exists_commonDescription_decoders D hD
  obtain ⟨cT, hT⟩ := exists_trivial_commonDescription_decoders D hD
  obtain ⟨cP, hP⟩ := condK_le_plainK D hD
  obtain ⟨cL, hL⟩ := plainK_le_length D hD
  refine ⟨6 * (cL + cP) + cS + cR + cT + 63,
    fun n α β γ x y z hx hy hz hxz hyz => ?_⟩
  have hslack : ∀ {a : ℕ∞} {k : ℕ}, k ≤ 6 * (cL + cP) + cS + cR + cT + 39 +
      24 * (Nat.bits n).length → a ≤ (k : ℕ∞) →
      a ≤ (logSlack (6 * (cL + cP) + cS + cR + cT + 63) n : ℕ∞) := by
    intro a k hk ha
    refine ha.trans ?_
    have hmul : 24 * (Nat.bits n).length ≤
        (6 * (cL + cP) + cS + cR + cT + 63) * (Nat.bits n).length :=
      Nat.mul_le_mul_right _ (by omega)
    unfold logSlack
    exact_mod_cast (by omega)
  have hxy := length_listCode_cons x [y]
  have hy' := length_listCode_cons y []
  simp only [listCode_nil, List.length_nil, add_zero] at hy'
  by_cases hsmall : (listCode [x, y]).length ≤ α
  · obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hT x y
    refine ⟨fun e => if e = (0, 1) then listCode [x, y] else if e = (1, 2) then x
      else if e = (1, 3) then y else [], ?_⟩
    exact commonInformationRequest_fulfilled_of_local D x y α β γ _ _ hsmall
      (Nat.zero_le _) (Nat.zero_le _)
      (hslack (by omega) h₁) (hslack (by omega) h₂) (hslack (by omega) h₂)
      (hslack (by omega) h₃) (hslack (by omega) h₄)
      (hslack (by omega) h₅) (hslack (by omega) h₆)
  · have hα : α ≤ 4 * n + (2 + (cL + cP)) := by omega
    obtain ⟨p₀, hp₀l, hp₀⟩ := (condK_le_iff D z [] α).mp hz
    have hcond : ∀ w : BitString, w.length ≤ n → ∀ δ : ℕ, condK D w z ≤ (δ : ℕ∞) →
        condK D w z ≤ ((min δ (n + (cL + cP)) : ℕ) : ℕ∞) := by
      intro w hw δ hδ
      rw [Nat.mono_cast.map_min]
      refine le_min hδ ?_
      calc condK D w z ≤ plainK D w + cP := hP w z
        _ ≤ (w.length : ℕ∞) + cL + cP := by gcongr; exact hL w
        _ ≤ ((n + (cL + cP) : ℕ) : ℕ∞) := by
          rw [add_assoc]; exact_mod_cast (by omega)
    obtain ⟨qx₀, hqx₀l, hqx₀⟩ := (condK_le_iff D x z _).mp (hcond x hx β hxz)
    obtain ⟨qy₀, hqy₀l, hqy₀⟩ := (condK_le_iff D y z _).mp (hcond y hy γ hyz)
    obtain ⟨p, qx, qy, z', hz', hx', hy'', hpl, hqxl, hqyl, hp, hqx, hqy⟩ :=
      hS α (min β (n + (cL + cP))) (min γ (n + (cL + cP))) x y p₀ qx₀ qy₀ z
        hp₀ hqx₀ hqy₀ hp₀l hqx₀l hqy₀l
    have hadv : (listCode [Nat.bits α, Nat.bits (min β (n + (cL + cP))),
        Nat.bits (min γ (n + (cL + cP)))]).length ≤
        24 * (Nat.bits n).length + 39 + 6 * (cL + cP) := by
      have e₁ := length_listCode_cons (Nat.bits α)
        [Nat.bits (min β (n + (cL + cP))), Nat.bits (min γ (n + (cL + cP)))]
      have e₂ := length_listCode_cons (Nat.bits (min β (n + (cL + cP))))
        [Nat.bits (min γ (n + (cL + cP)))]
      have e₃ := length_listCode_cons (Nat.bits (min γ (n + (cL + cP)))) []
      have b₁ := length_bits_le_of_le_four_mul_add n (2 + (cL + cP)) α hα
      have b₂ := length_bits_le_of_le_four_mul_add n (2 + (cL + cP))
        (min β (n + (cL + cP))) (by omega)
      have b₃ := length_bits_le_of_le_four_mul_add n (2 + (cL + cP))
        (min γ (n + (cL + cP))) (by omega)
      simp only [listCode_nil, List.length_nil, add_zero] at e₃
      omega
    have hnode : ∀ {w : BitString},
        condK D w (listCode [listCode [x, y]]) ≤
          ((listCode [Nat.bits α, Nat.bits (min β (n + (cL + cP))),
            Nat.bits (min γ (n + (cL + cP)))]).length : ℕ∞) + cS →
        condK D w (listCode [listCode [x, y]]) ≤
          (logSlack (6 * (cL + cP) + cS + cR + cT + 63) n : ℕ∞) := by
      intro w hw
      refine hslack (k := 24 * (Nat.bits n).length + 39 + 6 * (cL + cP) + cS) (by omega)
        (hw.trans ?_)
      exact_mod_cast (by omega)
    refine ⟨fun e => if e = (0, 1) then p else if e = (0, 2) then qx
      else if e = (0, 3) then qy else if e = (1, 2) then z' else if e = (1, 3) then z'
      else [], ?_⟩
    exact commonInformationRequest_fulfilled_of_local D x y α β γ _ _ hpl
      (hqxl.trans (min_le_left _ _)) (hqyl.trans (min_le_left _ _))
      (hnode hp) (hnode hqx) (hnode hqy)
      (hslack (by omega) (hR₁ p z' hz')) (hslack (by omega) (hR₁ p z' hz'))
      (hslack (by omega) (hR₂ qx z' x hx')) (hslack (by omega) (hR₂ qy z' y hy''))

end Kolmogorov
