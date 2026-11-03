/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Class.Enumeration
import KolmogorovMathlib.MDLPrediction.Class.Presentation

/-!
# Partial replay of complete discovery blocks

The partial replay has a value only for an ordinal whose whole block has appeared.
The final incomplete block is never treated as a halting replay computation.
Blueprint nodes: `enum:block-replay`.
-/

namespace Kolmogorov.MDLPrediction

/-- Search successive discovery prefixes until block `j` has all `2^r` members,
then return the presentation's mixture index for that block.
Blueprint node `enum:block-replay`. -/
noncomputable def blockReplay (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (a r j : ℕ) : Part ℕ :=
  (Nat.rfind fun n => Part.some (decide
    ((j + 1) * 2 ^ r ≤ ((List.range n).filterMap (discoveryStream U hU a)).length))).map
      (fun n => A.mix (ordinalBlock
        ((List.range n).filterMap (discoveryStream U hU a)) r j))

/-- Searching for a complete ordinal block is partial recursive. -/
private lemma blockReplay_partrec (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) :
    Partrec (fun p : ℕ × ℕ × ℕ => blockReplay U hU A p.1 p.2.1 p.2.2) := by
  have hS : Computable₂ (discoveryStream U hU) := (Classical.choose_spec (enum_indices_ce U hU)).1
  have hrec : ∀ a n, (List.range n).filterMap (discoveryStream U hU a) =
      Nat.rec (motive := fun _ => List ℕ) [] (fun y IH => IH ++ (discoveryStream U hU a
        y).toList) n := by
    intro a n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.filterMap_append, ih]
      change (Nat.rec (motive := fun _ => List ℕ) [] (fun y IH => IH ++ (discoveryStream U hU a
        y).toList) n) ++ (discoveryStream U hU a n).toList = _
      rfl
  have h1 : Computable (fun q : (ℕ × ℕ) × (ℕ × List ℕ) => discoveryStream U hU q.1.1 q.2.1) :=
    hS.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)
  have h2 : Computable (fun q : (ℕ × ℕ) × (ℕ × List ℕ) => (discoveryStream U hU q.1.1
    q.2.1).toList) :=
    Primrec.optionToList.to_comp.comp h1
  have hh : Computable₂ (fun (q : ℕ × ℕ) (p : ℕ × List ℕ) => p.2 ++ (discoveryStream U hU q.1
    p.1).toList) :=
    Primrec.list_append.to_comp.comp (Computable.snd.comp Computable.snd) h2
  have h : Computable (fun q : ℕ × ℕ => Nat.rec (motive := fun _ => List ℕ) [] (fun y IH => IH
    ++ (discoveryStream U hU q.1 y).toList) q.2) :=
    Computable.nat_rec (f := fun q : (ℕ × ℕ) => q.2) (g := fun _ => ([] : List ℕ))
      Computable.snd (Computable.const []) hh
  have hpow : Computable₂ (fun (a b : ℕ) => a ^ b) := Primrec.nat_iff.mpr Nat.Primrec.pow |>.to_comp
  have hsize : Computable (fun x : (ℕ × ℕ × ℕ) × ℕ => 2 ^ x.1.2.1) :=
    hpow.comp (Computable.const 2) (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hstart : Computable (fun x : (ℕ × ℕ × ℕ) × ℕ => x.1.2.2 * 2 ^ x.1.2.1) :=
    Primrec.nat_mul.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)) hsize
  have hend : Computable (fun x : (ℕ × ℕ × ℕ) × ℕ => (x.1.2.2 + 1) * 2 ^ x.1.2.1) :=
    Primrec.nat_mul.to_comp.comp (Computable.succ.comp (Computable.snd.comp
      (Computable.snd.comp Computable.fst))) hsize
  have hpair : Computable (fun x : (ℕ × ℕ × ℕ) × ℕ => (x.1.1, x.2)) :=
    (Computable.fst.comp Computable.fst).pair Computable.snd
  have hlist : Computable (fun x : (ℕ × ℕ × ℕ) × ℕ => (List.range x.2).filterMap
    (discoveryStream U hU x.1.1)) :=
    (h.comp hpair).of_eq (fun x => (hrec x.1.1 x.2).symm)
  have hlen : Computable (fun x : (ℕ × ℕ × ℕ) × ℕ => ((List.range x.2).filterMap
    (discoveryStream U hU x.1.1)).length) :=
    Computable.list_length.comp hlist
  have htest : Computable₂ (fun (p : ℕ × ℕ × ℕ) n => decide ((p.2.2 + 1) * 2 ^ p.2.1 ≤
    ((List.range n).filterMap (discoveryStream U hU p.1)).length)) :=
    Primrec.nat_le.decide.to_comp.comp hend hlen
  have hblock : Computable₂ (fun (p : ℕ × ℕ × ℕ) n => ordinalBlock ((List.range n).filterMap
    (discoveryStream U hU p.1)) p.2.1 p.2.2) :=
    Primrec.list_take.to_comp.comp hsize (Primrec.list_drop.to_comp.comp hstart hlist)
  have hval : Computable₂ (fun (p : ℕ × ℕ × ℕ) n => A.mix (ordinalBlock ((List.range
    n).filterMap (discoveryStream U hU p.1)) p.2.1 p.2.2)) :=
    A.mix_computable.comp hblock
  have ptest : Partrec₂ (fun (p : ℕ × ℕ × ℕ) n => (Part.some (decide ((p.2.2 + 1) * 2 ^ p.2.1 ≤
    ((List.range n).filterMap (discoveryStream U hU p.1)).length)) : Part Bool)) := htest.partrec₂
  exact (Partrec.map (Partrec.rfind ptest) hval).of_eq fun _ => rfl

/-- The replay search halts on every complete block. -/
private lemma blockReplay_halts (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) :
    ∀ a r j G, IsCompleteBlock U hU a r j G →
      A.mix G ∈ blockReplay U hU A a r j := by
  rintro a r j G ⟨n, hG, hlen⟩
  let L := fun k => (List.range k).filterMap (discoveryStream U hU a)
  have h_len_G : G.length = min (2 ^ r) ((L n).length - j * 2 ^ r) := by
    calc G.length = (ordinalBlock (L n) r j).length := congrArg List.length hG
      _ = min (2 ^ r) ((L n).length - j * 2 ^ r) := by
        simp only [ordinalBlock, List.length_take, List.length_drop]
  have hn : (j + 1) * 2 ^ r ≤ (L n).length := by
    have hp : 0 < 2 ^ r := by positivity
    have h_min : 2 ^ r = min (2 ^ r) ((L n).length - j * 2 ^ r) := by
      calc 2 ^ r = G.length := hlen.symm
        _ = min (2 ^ r) ((L n).length - j * 2 ^ r) := h_len_G
    have h1 : 2 ^ r ≤ (L n).length - j * 2 ^ r := by omega
    rw [add_mul, one_mul]
    omega
  let p := fun k => decide ((j + 1) * 2 ^ r ≤ (L k).length)
  have pn : p n = true := decide_eq_true hn
  obtain ⟨m, hm, hmn⟩ := Nat.rfind_min' pn
  have hm_spec : (j + 1) * 2 ^ r ≤ (L m).length := by
    have h1 := Nat.rfind_spec hm
    simp only [PFun.coe_val, Part.mem_some_iff] at h1
    exact of_decide_eq_true h1.symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hblock : ordinalBlock (L m) r j = G := by
    have L_eq : L (m + k) = L m ++ (List.map (fun x => m + x) (List.range k)).filterMap
        (discoveryStream U hU a) := by
      change (List.range (m + k)).filterMap (discoveryStream U hU a) = _
      rw [List.range_add, List.filterMap_append]
    rw [hG]
    change ordinalBlock (L m) r j = ordinalBlock (L (m + k)) r j
    rw [L_eq]
    unfold ordinalBlock
    have h1 : j * 2 ^ r ≤ (L m).length := by
      have : (j + 1) * 2 ^ r = j * 2 ^ r + 2 ^ r := by rw [add_mul, one_mul]
      omega
    have h2 : 2 ^ r ≤ (L m).length - j * 2 ^ r := by
      have : (j + 1) * 2 ^ r = j * 2 ^ r + 2 ^ r := by rw [add_mul, one_mul]
      omega
    rw [List.drop_append_of_le_length h1]
    rw [List.take_append_of_le_length (by rw [List.length_drop]; omega)]
  rw [← hblock]
  have hm' : m ∈ Nat.rfind (fun n => Part.some (p n)) := hm
  exact Part.mem_map (fun k => A.mix (ordinalBlock (L k) r j)) hm'

/-- The replay algorithm halts for each complete block, returns its mixture index,
and is partial recursive in the block parameters. Blueprint node `enum:block-replay`. -/
theorem enum_block_replay (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) :
    Partrec (fun p : ℕ × ℕ × ℕ => blockReplay U hU A p.1 p.2.1 p.2.2) ∧
      ∀ a r j G, IsCompleteBlock U hU a r j G →
        A.mix G ∈ blockReplay U hU A a r j :=
  ⟨blockReplay_partrec U hU A, blockReplay_halts U hU A⟩
end Kolmogorov.MDLPrediction
