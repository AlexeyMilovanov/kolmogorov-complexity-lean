import KolmogorovMathlib.MonotoneComplexity.GacsDayFamilyGame

/-!
# The request scale of the Gacs-Day endgame

The endgame plays its family game at the dyadic scale `2 ^ (-a)` with
`a = grayEndgameA d = Nat.size (4 * d)`, which is the coarsest scale that still
fits under the budget `1 / d`:

  `4 * d < 2 ^ grayEndgameA d ≤ 8 * d`.

Only the scale, its two bounds and the computability facts the strategy lift
needs live here; they are controller-independent and are consumed by the pinned
single-call endgame.
-/

namespace Kolmogorov

/-- The dyadic request scale `2 ^ (-a)` of every tree of the endgame family, used
both as the request scale `alphaDepth` and as the gray scale `epsDepth`. -/
def grayEndgameA (d : ℕ) : ℕ := Nat.size (4 * d)

/-- The budget `1 / d` of the strategy lift is computable in `d`. -/
lemma computable_one_div_d : Computable (fun d : ℕ => 1 / (d : ℚ)) := by
  let N (d : ℕ) : ℤ := Nat.casesOn d 0 (fun _ => 1)
  let D (d : ℕ) : ℕ := Nat.casesOn d 1 (fun d' => d' + 1)
  have hN : Computable N := by
    have hc : Computable₂ (fun (_ _ : ℕ) => (1 : ℤ)) := Computable.const 1
    apply Computable.nat_casesOn Computable.id (Computable.const 0) hc
  have hD : Computable D := by
    have hs : Computable₂ (fun (_ d' : ℕ) => d' + 1) := Primrec.succ.to_comp.comp Computable.snd
    apply Computable.nat_casesOn Computable.id (Computable.const 1) hs
  apply computable_of_num_den (N := N) (D := D) hN hD
  · intro d
    cases d <;> simp [D]
  · intro d
    cases d <;> simp [N, D]

/-- The endgame scale `grayEndgameA` is computable. -/
lemma computable_grayEndgame_a : Computable grayEndgameA := by
  have hmul : Computable (fun d : ℕ => 4 * d) :=
    Primrec.to_comp (Primrec.nat_mul.comp (Primrec.const 4) Primrec.id)
  exact computable_nat_size.comp hmul

/-- The endgame scale is at least `1` from depth `1` on. -/
lemma one_le_grayEndgame_a {d : ℕ} (hd : 1 ≤ d) : 1 ≤ grayEndgameA d := by
  have hpos : 0 < 4 * d := by positivity
  exact Nat.size_pos.mpr hpos

/-- The request scale is fine enough for the budget and coarse enough for the
measure barrier: `4 * d < 2 ^ a ≤ 8 * d`. -/
lemma grayEndgame_a_bounds {d : ℕ} (hd : 1 ≤ d) :
    4 * d < 2 ^ grayEndgameA d ∧ 2 ^ grayEndgameA d ≤ 8 * d := by
  have hpos : 0 < 4 * d := by omega
  have hs : 0 < Nat.size (4 * d) := Nat.size_pos.mpr hpos
  refine ⟨Nat.lt_size_self _, ?_⟩
  have h1 : 2 ^ (Nat.size (4 * d) - 1) ≤ 4 * d :=
    (Nat.lt_size (m := Nat.size (4 * d) - 1) (n := 4 * d)).mp (by omega)
  have h2 : 2 ^ grayEndgameA d = 2 * 2 ^ (Nat.size (4 * d) - 1) := by
    change 2 ^ Nat.size (4 * d) = _
    conv_lhs => rw [show Nat.size (4 * d) = (Nat.size (4 * d) - 1) + 1 by omega]
    ring
  omega

end Kolmogorov
