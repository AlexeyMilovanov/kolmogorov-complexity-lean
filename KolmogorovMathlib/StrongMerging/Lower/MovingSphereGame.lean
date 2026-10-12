import KolmogorovMathlib.StrongMerging.Lower.CenterCode
import KolmogorovMathlib.StrongMerging.Lower.Reservoir

/-!
# The sharp lower bound: the Hamming instance of the reservoir game

The instance of the generic reservoir game (nodes L14-L21, `Lower/Reservoir*.lean`) used by the
moving-sphere reservoir (node L23, `Lower/MovingSphere.lean`), for the blueprint paragraphs
"L22--L23" (lines ~4784-4806) and the paper's proof of Lemma `lem:ham-reservoir`.

* `hammingGame M R ℓ δ`: the cube `{0,1}^M` (`allStrings M`, canonical order), the spheres
  `S_z = hammingSphere |z| z R`, `N = (M choose R)`.
* `hammingSources cV cT K S τ`: the three candidate families of node L14 read through the bounded
  evaluators (`conditionalRunOut`) of a code `cV` of the plain machine `V` and a code `cT` of the
  canonical total interpreter: the ordinary programs shorter than `K` (point events), the ordinary
  programs of length at most `K + τ` (set events, cost = program length) and the total-interpreter
  programs of length at most `S` (table events).  Candidates are numbered in shortlex order
  (`shortlexWord`).
* `hammingGameHyp`: the hypotheses `GameHyp` of the generic game, from sphere incidence (L06), the
  heavy-cell bound (L09) and the four game inequalities (`ReservoirInequalities`).
* `point_event_of_plainC_lt`, `set_event_of_score_le`, `table_event_of_partition`: completeness of
  the stream for low-complexity points, low-score sets and exact partition programs.
* `hammingEmit`: the stream of emitted centers, through the natural-number image of the game
  (`ReservoirTransport`), computable and prefix-monotone (`hammingEmit_computable`,
  `hammingEmit_mono`), and equal to the emitted centers of `hammingGame` (`hammingEmit_eq`).
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

/-! ### Sphere lists -/

/-- The sphere of radius `R` around `z` (in the cube of dimension `|z|`), listed in the canonical
order of `allStrings`. -/
def sphereList (R : ℕ) (z : BitString) : List BitString :=
  (allStrings z.length).filter fun u => hammingDist z u = R

/-- **Membership in the sphere list**: `u ∈ sphereList R z ↔ u ∈ S_z = hammingSphere |z| z R`.
Reference: paper line 1499 ("its index in the full sphere"); node L23. -/
theorem mem_sphereList_iff (R : ℕ) (z u : BitString) :
    u ∈ sphereList R z ↔ u ∈ hammingSphere z.length z R := by
  rw [sphereList, List.mem_filter, hammingSphere, Finset.mem_filter, mem_allStrings,
    mem_stringsOfLength, decide_eq_true_eq]

/-- Membership in a Hamming sphere: `u ∈ hammingSphere n x s ↔ |u| = n ∧ dist(x, u) = s`. -/
theorem mem_hammingSphere_iff {n s : ℕ} {x u : BitString} :
    u ∈ hammingSphere n x s ↔ u.length = n ∧ hammingDist x u = s := by
  rw [hammingSphere, Finset.mem_filter, mem_stringsOfLength]

/-- **Length of the sphere list**: `|sphereList R z| = (|z| choose R)`.
Reference: paper lines 1279-1284 (`N = (M choose R)`); node L06, L23. -/
theorem length_sphereList (R : ℕ) (z : BitString) :
    (sphereList R z).length = z.length.choose R := by
  have hnd : (sphereList R z).Nodup := (allStrings_nodup _).filter _
  rw [← List.toFinset_card_of_nodup hnd, ← hammingSphere_card z.length z R rfl]
  congr 1
  ext u
  rw [List.mem_toFinset, mem_sphereList_iff]

/-- **Sphere lists are primitive recursive** in the radius and the center. -/
theorem sphereList_primrec : Primrec₂ sphereList := by
  have hf : Primrec fun p : ℕ × BitString => allStrings p.2.length :=
    CodedFiniteDistribution.allStrings_primrec.comp (Primrec.list_length.comp Primrec.snd)
  have hp : Primrec₂ fun (p : ℕ × BitString) (u : BitString) =>
      decide (hammingDist p.2 u = p.1) :=
    primrec_decideEq.comp (hammingDist_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  exact (list_filter_primrec hf hp).of_eq fun _ => rfl

/-- **The sphere family is computable**: `(ps, y) ↦ sphereList (ps.getD 0 0) y`.
Reference: blueprint L23 ("center-plus-full-sphere index"). -/
theorem sphereFamily_computable :
    Computable₂ fun (ps : List ℕ) (y : BitString) => sphereList (ps.getD 0 0) y :=
  sphereList_primrec.to_comp.comp
    ((Primrec.list_getD 0).to_comp.comp Computable.fst (Computable.const 0)) Computable.snd

/-! ### Shortlex numbering of programs -/

/-- The `c`-th binary word in shortlex order: the binary expansion of `c + 1` without its leading
one (`Nat.bits` is little-endian, so the leading one is its last bit).  The words of length `< K`
are exactly the `shortlexWord c` with `c < 2^K - 1`. -/
def shortlexWord (c : ℕ) : BitString :=
  (Nat.bits (c + 1)).dropLast

/-- The binary value of a word ending in `true` is positive. -/
theorem decodeBits_append_true_pos (l : BitString) : 0 < decodeBits (l ++ [true]) := by
  induction l with
  | nil => simp [decodeBits]
  | cons b t ih => cases b <;> simp only [List.cons_append, decodeBits] <;> omega

/-- The binary value of a word of length `L` is below `2^L`. -/
theorem decodeBits_lt_two_pow (l : BitString) : decodeBits l < 2 ^ l.length := by
  induction l with
  | nil => simp [decodeBits]
  | cons b t ih => cases b <;> simp only [decodeBits, List.length_cons, pow_succ] <;> omega

/-- `Nat.bits` inverts `decodeBits` on words ending in `true`. -/
theorem natBits_decodeBits_append_true (l : BitString) :
    Nat.bits (decodeBits (l ++ [true])) = l ++ [true] := by
  induction l with
  | nil =>
    have h1 : decodeBits ([] ++ [true]) = Nat.bit true 0 := rfl
    rw [h1, Nat.bits_append_bit 0 true (fun _ => rfl), Nat.zero_bits]
    rfl
  | cons b t ih =>
    have hpos := decodeBits_append_true_pos t
    have hbit : decodeBits ((b :: t) ++ [true]) = Nat.bit b (decodeBits (t ++ [true])) := by
      cases b <;> simp [decodeBits, Nat.bit_val]
    rw [hbit, Nat.bits_append_bit _ _ (fun h => absurd h hpos.ne'), ih]
    rfl

/-- **Every word is a shortlex word of small index**: `p = shortlexWord c` for some `c` with
`c + 1 < 2^(|p| + 1)` (take `c + 1 = decodeBits (p ++ [true])`).
Reference: blueprint L14 ("finite sets of candidate program bodies"). -/
theorem exists_shortlexWord (p : BitString) :
    ∃ c : ℕ, shortlexWord c = p ∧ c + 1 < 2 ^ (p.length + 1) := by
  have hpos := decodeBits_append_true_pos p
  refine ⟨decodeBits (p ++ [true]) - 1, ?_, ?_⟩
  · rw [shortlexWord, Nat.sub_add_cancel (Nat.succ_le_of_lt hpos),
      natBits_decodeBits_append_true, List.dropLast_concat]
  · rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)]
    have h := decodeBits_lt_two_pow (p ++ [true])
    rwa [List.length_append, List.length_singleton] at h

/-- The binary expansion of a positive number ends with its leading one. -/
theorem natBits_eq_append_true {n : ℕ} (hn : n ≠ 0) : ∃ l, Nat.bits n = l ++ [true] := by
  induction n using Nat.binaryRec with
  | zero => exact absurd rfl hn
  | bit b m ih =>
    by_cases hm : m = 0
    · subst hm
      cases b
      · exact absurd rfl hn
      · exact ⟨[], by rw [Nat.bits_append_bit 0 true (fun _ => rfl), Nat.zero_bits]; rfl⟩
    · obtain ⟨l, hl⟩ := ih hm
      exact ⟨b :: l, by rw [Nat.bits_append_bit _ _ (fun h => absurd h hm), hl]; rfl⟩

/-- `Nat.bits (c + 1)` is the shortlex word of `c` followed by the leading one. -/
theorem natBits_succ_eq (c : ℕ) : Nat.bits (c + 1) = shortlexWord c ++ [true] := by
  obtain ⟨l, hl⟩ := natBits_eq_append_true (Nat.succ_ne_zero c)
  rw [shortlexWord, hl, List.dropLast_concat]

/-- The shortlex numbering is injective. -/
theorem shortlexWord_injective : Function.Injective shortlexWord := by
  intro a b h
  have h' : Nat.bits (a + 1) = Nat.bits (b + 1) := by rw [natBits_succ_eq, natBits_succ_eq, h]
  exact Nat.succ_injective (natBits_injective h')

/-- **At most `2^i` candidates of cost `i`**: among the first `n` shortlex words, at most `2^i`
have length `i` (the numbering is injective and there are `2^i` words of length `i`).
Reference: blueprint L14 ("at most `∑ 2^i` set-program events"). -/
theorem shortlex_cost_count (n i : ℕ) :
    ((List.range n).filter fun c => (shortlexWord c).length == i).length ≤ 2 ^ i := by
  have hnd : ((List.range n).filter fun c => (shortlexWord c).length == i).Nodup :=
    (List.nodup_range).filter _
  rw [← List.length_map (f := shortlexWord),
    ← List.toFinset_card_of_nodup (hnd.map shortlexWord_injective), ← card_stringsOfLength i]
  apply Finset.card_le_card
  intro w hw
  rw [List.mem_toFinset, List.mem_map] at hw
  obtain ⟨c, hc, rfl⟩ := hw
  rw [mem_stringsOfLength]
  have h := (List.mem_filter.1 hc).2
  rwa [beq_iff_eq] at h

/-- **Shortlex words are computable** (`dropLast = take (length - 1)` of `Nat.bits (c + 1)`).
Reference: blueprint L14. -/
theorem shortlexWord_computable : Computable shortlexWord := by
  have hb : Computable fun c : ℕ => Nat.bits (c + 1) := natBits_computable.comp Computable.succ
  exact (Primrec.list_take.to_comp.comp
    (Primrec.nat_sub.to_comp.comp (Computable.list_length.comp hb) (Computable.const 1)) hb).of_eq
    fun c => by rw [shortlexWord, List.dropLast_eq_take]

/-! ### The Hamming game and its event sources -/

/-- **The Hamming instance of the reservoir game**: the cube `{0,1}^M` in the canonical order of
`allStrings M`, spheres `S_z = hammingSphere |z| z R` (for centers, `|z| = M`), sphere size
`N = (M choose R)`, heaviness exponents `ℓ, δ`, fallback the zero word. -/
def hammingGame (M R ℓ δ : ℕ) : ResGame BitString where
  centers := allStrings M
  sphere z := hammingSphere z.length z R
  N := M.choose R
  ell := ℓ
  delta := δ
  fallback := List.replicate M false

/-- **The event sources of the Hamming instance** (node L14): candidates are numbered in shortlex
order; point candidates are the `2^K - 1` ordinary programs shorter than `K`, run by the bounded
evaluator of the code `cV` with the empty condition; set candidates are the `2^(K+τ+1) - 1`
ordinary programs of length at most `K + τ`, whose outputs are decoded as finite models, with
certificate cost the program length; table candidates are the `2^(S+1) - 1` programs of length at
most `S` of the total interpreter (code `cT`), run on each cube point. -/
noncomputable def hammingSources (cV cT : Nat.Partrec.Code) (K S τ : ℕ) :
    EventSources BitString where
  numPt := 2 ^ K - 1
  ptEval c s := conditionalRunOut cV s (shortlexWord c) []
  numSet := 2 ^ (K + τ + 1) - 1
  setEval c s := (conditionalRunOut cV s (shortlexWord c) []).map decodeModel
  setCost c := (shortlexWord c).length
  numTab := 2 ^ (S + 1) - 1
  tabEval c u s := (conditionalRunOut cT s (shortlexWord c) u).map decodeModel

/-- The cube of the Hamming game is `stringsOfLength M`. -/
theorem hammingGame_cube (M R ℓ δ : ℕ) : (hammingGame M R ℓ δ).cube = stringsOfLength M :=
  rfl

/-! ### The hypotheses of the generic game -/

/-- **Sphere incidence of the Hamming game**: every word lies in at most `N = (M choose R)`
spheres around centers (the centers whose sphere contains `u` form the sphere of radius `R`
around `u`, or nothing if `|u| ≠ M`).
Reference: paper lines 1448-1452 (uniform sphere average); node L06, L16. -/
theorem hammingGame_incidence (M R ℓ δ : ℕ) (u : BitString) :
    ((hammingGame M R ℓ δ).centers.filter fun z =>
      decide (u ∈ (hammingGame M R ℓ δ).sphere z)).length ≤ (hammingGame M R ℓ δ).N := by
  change ((allStrings M).filter fun z => decide (u ∈ hammingSphere z.length z R)).length ≤
    M.choose R
  have hnd : ((allStrings M).filter fun z => decide (u ∈ hammingSphere z.length z R)).Nodup :=
    (allStrings_nodup M).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  by_cases huM : u.length = M
  · rw [← hammingSphere_card M u R huM]
    apply Finset.card_le_card
    intro z hz
    rw [List.mem_toFinset, List.mem_filter, mem_allStrings, decide_eq_true_eq] at hz
    obtain ⟨hzM, hu⟩ := hz
    rw [hzM] at hu
    exact (mem_hammingSphere_comm huM hzM).1 hu
  · have hnil : ((allStrings M).filter fun z => decide (u ∈ hammingSphere z.length z R)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro z hz
      rw [mem_allStrings] at hz
      rw [decide_eq_true_eq, mem_hammingSphere_iff, hz]
      exact fun h => huM h.1
    rw [hnil]
    simp

/-- **The heavy-cell bound of the Hamming game** (node L09 in the form of `GameHyp`): for every
exact cell partition `P` of the cube, `∑_z |heavy points of P in S_z| ≤ 2^M N θ`.  With `Q u` the
cell of `P` containing `u` (`∅` off the cube), the sum is at most the number of heavy pairs
`heavyPairs M R ℓ δ Q`, bounded by `partitionHeavyBound_of_cells`.
Reference: paper lines 1452-1456; blueprint L16, L09. -/
theorem hammingGame_heavy_bound {M R ℓ δ h : ℕ} (hR : 0 < R) (h2R : 2 * R < M) (hh : 1 ≤ h)
    (P : List (Finset BitString)) (hP : IsCellPartition (hammingGame M R ℓ δ).cube P) :
    ((∑ z ∈ (hammingGame M R ℓ δ).cube,
      (tableHeavyPoints (hammingGame M R ℓ δ) P z).card : ℕ) : ℝ) ≤
      ((hammingGame M R ℓ δ).cube.card : ℝ) * (hammingGame M R ℓ δ).N *
        heavyTheta M R ℓ δ h := by
  obtain ⟨hsub, -, huniq⟩ := hP
  set cell : BitString → Finset BitString := fun u => (P.filter fun Q => decide (u ∈ Q)).headD ∅
  have hcell_sub : ∀ u, cell u ⊆ stringsOfLength M := by
    intro u
    change (P.filter fun Q => decide (u ∈ Q)).headD ∅ ⊆ stringsOfLength M
    cases hl : P.filter fun Q => decide (u ∈ Q) with
    | nil => exact Finset.empty_subset _
    | cons Q t =>
      have hQ : Q ∈ P.filter fun Q => decide (u ∈ Q) := by rw [hl]; simp
      exact (hsub Q (List.mem_filter.1 hQ).1).2
  have hcell_eq : ∀ Q ∈ P, ∀ u ∈ Q, cell u = Q := by
    intro Q hQ u huQ
    change (P.filter fun Q => decide (u ∈ Q)).headD ∅ = Q
    cases hl : P.filter fun Q => decide (u ∈ Q) with
    | nil =>
      have hm : Q ∈ P.filter fun Q => decide (u ∈ Q) :=
        List.mem_filter.2 ⟨hQ, decide_eq_true huQ⟩
      rw [hl] at hm
      simp at hm
    | cons Q' t =>
      have hQ' : Q' ∈ P.filter fun Q => decide (u ∈ Q) := by rw [hl]; simp
      have h1 := List.mem_filter.1 hQ'
      exact huniq Q' h1.1 Q hQ u (of_decide_eq_true h1.2) huQ
  have hbound := partitionHeavyBound_of_cells M R ℓ δ h hR h2R.le hh cell hcell_sub
  have hpairs : (heavyPairs M R ℓ δ cell).card = ∑ z ∈ stringsOfLength M,
      ((stringsOfLength M).filter fun u => u ∈ hammingSphere M z R ∧ 2 ^ ℓ ≤ (cell u).card ∧
        (cell u).card < 2 ^ δ * (cell u ∩ hammingSphere M z R).card).card := by
    rw [heavyPairs, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.card_filter]
  have hle : (∑ z ∈ stringsOfLength M, (tableHeavyPoints (hammingGame M R ℓ δ) P z).card) ≤
      (heavyPairs M R ℓ δ cell).card := by
    rw [hpairs]
    refine Finset.sum_le_sum fun z hz => Finset.card_le_card fun u hu => ?_
    have hzM : z.length = M := (mem_stringsOfLength M z).1 hz
    rw [tableHeavyPoints, Finset.mem_filter] at hu
    obtain ⟨huS, Q, hQP, huQ, hheavy1, hheavy2⟩ := hu
    have huS' : u ∈ hammingSphere M z R := by rw [← hzM]; exact huS
    have hcQ : cell u = Q := hcell_eq Q hQP u huQ
    rw [Finset.mem_filter, hcQ]
    refine ⟨(Finset.mem_filter.1 huS').1, huS', hheavy1, ?_⟩
    rw [← hzM]
    exact hheavy2
  have hNpos : (0 : ℝ) < 2 ^ M * M.choose R := by
    have : 0 < M.choose R := Nat.choose_pos (by omega)
    positivity
  have hb := (div_le_iff₀ hNpos).1 hbound
  have hle' : ((∑ z ∈ stringsOfLength M, (tableHeavyPoints (hammingGame M R ℓ δ) P z).card : ℕ) :
      ℝ) ≤ (heavyPairs M R ℓ δ cell).card := by exact_mod_cast hle
  change ((∑ z ∈ stringsOfLength M, (tableHeavyPoints (hammingGame M R ℓ δ) P z).card : ℕ) :
      ℝ) ≤ ((stringsOfLength M).card : ℝ) * (M.choose R : ℕ) * heavyTheta M R ℓ δ h
  rw [card_stringsOfLength]
  calc _ ≤ ((heavyPairs M R ℓ δ cell).card : ℝ) := hle'
    _ ≤ 2 ^ δ * (hammingVol M (h - 1) / 2 ^ ℓ + collisionBeta M R ^ h) *
        (2 ^ M * M.choose R) := hb
    _ = _ := by
      unfold heavyTheta
      push_cast
      ring

/-- The heavy-cell constant is nonnegative (`β ≥ 0`, `collisionBeta_nonneg_le_one`). -/
theorem heavyTheta_nonneg (M R ℓ δ h : ℕ) : 0 ≤ heavyTheta M R ℓ δ h := by
  have hb := (collisionBeta_nonneg_le_one M R).1
  unfold heavyTheta
  positivity

/-- **The Hamming game satisfies the hypotheses of the generic game** for the heavy-cell constant
`θ = heavyTheta M R ℓ δ h`, given `0 < R`, `2R < M`, `h ≥ 1` and the four game inequalities. -/
theorem hammingGameHyp {M R K S τ ℓ δ h : ℕ} (hR : 0 < R) (h2R : 2 * R < M) (hh : 1 ≤ h)
    (hineq : ReservoirInequalities M R K S τ ℓ δ h) :
    GameHyp (hammingGame M R ℓ δ) K τ S (heavyTheta M R ℓ δ h) where
  centers_nodup := allStrings_nodup M
  centers_ne_nil := by
    intro h0
    have := length_allStrings M
    rw [show allStrings M = [] from h0] at this
    exact absurd this.symm (by positivity)
  sphere_card := fun z hz => by
    have hz' : z.length = M := (mem_allStrings M z).1 hz
    change (hammingSphere z.length z R).card = M.choose R
    rw [hz']
    exact hammingSphere_card M z R hz'
  incidence := hammingGame_incidence M R ℓ δ
  heavy_bound := hammingGame_heavy_bound hR h2R hh
  theta_nonneg := heavyTheta_nonneg M R ℓ δ h
  density := by
    change 256 * (2 ^ K + (K + τ + 1) * 2 ^ (K + τ)) ≤ (allStrings M).length
    rw [length_allStrings]
    exact hineq.density
  heavy := hineq.heavy
  charge := hineq.charge
  arrivals := hineq.arrivals

/-! ### The event stream of the Hamming instance -/

/-- **The count hypotheses of the Hamming stream** (the premises of
`reservoirEventEnumeration`): fewer than `2^K` point candidates, at most `2^i` set candidates of
cost `i`, fewer than `2^(S+1)` table candidates. -/
theorem hammingSources_counts (cV cT : Nat.Partrec.Code) (K S τ : ℕ) :
    (hammingSources cV cT K S τ).numPt < 2 ^ K ∧
      (∀ i, ((List.range (hammingSources cV cT K S τ).numSet).filter fun c =>
        (hammingSources cV cT K S τ).setCost c == i).length ≤ 2 ^ i) ∧
      (hammingSources cV cT K S τ).numTab < 2 ^ (S + 1) := by
  refine ⟨Nat.sub_lt (by positivity) one_pos, fun i => shortlex_cost_count _ i,
    Nat.sub_lt (by positivity) one_pos⟩

/-- **The Hamming stream is valid at every stage**: by `reservoirEventEnumeration`, the event
history satisfies the L14 count/certificate invariants `ValidHistory` at every stage. -/
theorem hammingHistory_valid (cV cT : Nat.Partrec.Code) (M R K S τ ℓ δ : ℕ) (s : ℕ) :
    ValidHistory (hammingGame M R ℓ δ) K τ S
      (eventHistory (hammingGame M R ℓ δ) K τ (hammingSources cV cT K S τ) s) := by
  obtain ⟨hpt, hset, htab⟩ := hammingSources_counts cV cT K S τ
  exact (reservoirEventEnumeration (hammingGame M R ℓ δ) K τ S _ hpt hset htab).2.1 s

/-- **Completeness for low-complexity points**: if a cube point `u` has `C(u) < K` then its point
event eventually arrives.  A shortest program (`exists_program_of_condC`) is a shortlex candidate
of index `< 2^K - 1` (`exists_shortlexWord`); its bounded evaluation eventually succeeds
(`conditionalRunOut_complete`) and stays (`conditionalRunOut_mono`); apply
`point_mem_eventHistory`. -/
theorem point_event_of_plainC_lt {V : Map} (hV : isOptimalConditional V)
    {cV : Nat.Partrec.Code} (hcV : IsCodeFor cV V) (cT : Nat.Partrec.Code)
    (M R K S τ ℓ δ : ℕ) {u : BitString} (hu : u.length = M) (hC : plainC V u < K) :
    ∃ t, ResEvent.point u ∈
      eventHistory (hammingGame M R ℓ δ) K τ (hammingSources cV cT K S τ) t := by
  obtain ⟨p, hp, hlen⟩ := exists_program_of_condC V hV u []
  have hplt : p.length < K := by
    have : (p.length : ℝ) < K := by rw [hlen]; exact hC
    exact_mod_cast this
  obtain ⟨c, rfl, hc⟩ := exists_shortlexWord p
  obtain ⟨s, hs⟩ := conditionalRunOut_complete hcV hp
  have hcK : c < (hammingSources cV cT K S τ).numPt := by
    change c < 2 ^ K - 1
    have : 2 ^ ((shortlexWord c).length + 1) ≤ 2 ^ K :=
      Nat.pow_le_pow_right (by norm_num) hplt
    omega
  refine point_mem_eventHistory (hammingGame M R ℓ δ) K τ (hammingSources cV cT K S τ)
    (fun c' s' t' u' hst h => conditionalRunOut_mono cV hst h) hcK hs ?_
  change u ∈ (allStrings M).toFinset
  rw [List.mem_toFinset, mem_allStrings]
  exact hu

/-- **From a real score bound to the integer eligibility bound**: if `i + log₂ n ≤ k` (reals) with
`n > 0`, then `n 2^i ≤ 2^k` and `i ≤ k`.
Reference: paper lines 1405-1409 ("`2^ℓ ≤ |Q| ≤ 2^(K+τ-i)`"). -/
theorem card_mul_two_pow_le_of_logb {i k n : ℕ} (hn : 0 < n)
    (h : (i : ℝ) + Real.logb 2 n ≤ k) : n * 2 ^ i ≤ 2 ^ k ∧ i ≤ k := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg one_lt_two hn1
  have hik : i ≤ k := by
    have : (i : ℝ) ≤ k := by linarith
    exact_mod_cast this
  refine ⟨?_, hik⟩
  have hlog : Real.logb 2 (n : ℝ) ≤ ((k - i : ℕ) : ℝ) := by
    rw [Nat.cast_sub hik]
    linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (n : ℝ) ≤ (2 : ℝ) ^ ((k - i : ℕ) : ℝ) :=
    (Real.logb_le_iff_le_rpow one_lt_two hnpos).1 hlog
  rw [Real.rpow_natCast] at hle
  have hle' : n ≤ 2 ^ (k - i) := by exact_mod_cast hle
  calc n * 2 ^ i ≤ 2 ^ (k - i) * 2 ^ i := Nat.mul_le_mul_right _ hle'
    _ = 2 ^ k := by rw [← pow_add, Nat.sub_add_cancel hik]

/-- **Completeness for low-score sets**: if a set `Q` of `M`-words has `|Q| ≥ 2^ℓ` and
`C(Q) + log₂ |Q| ≤ K + τ`, then a set event `(Q, i)` (with `i = C(Q)`) eventually arrives.  A
shortest program for the canonical code of `Q` is a shortlex candidate of index
`< 2^(K+τ+1) - 1`; its bounded evaluation eventually prints the code, which decodes to `Q`
(`decodeModel_canonicalFiniteSetCode`); eligibility is `card_mul_two_pow_le_of_logb`. -/
theorem set_event_of_score_le {V : Map} (hV : isOptimalConditional V)
    {cV : Nat.Partrec.Code} (hcV : IsCodeFor cV V) (cT : Nat.Partrec.Code)
    (M R K S τ ℓ δ : ℕ) {Q : Finset BitString} (hQM : ∀ y ∈ Q, y.length = M)
    (hQℓ : 2 ^ ℓ ≤ Q.card) (hscore : setC V Q + Real.logb 2 Q.card ≤ K + τ) :
    ∃ t i, ResEvent.set Q i ∈
      eventHistory (hammingGame M R ℓ δ) K τ (hammingSources cV cT K S τ) t := by
  obtain ⟨p, hp, hlen⟩ := exists_program_of_condC V hV (canonicalFiniteSetCode Q) []
  have hQpos : 0 < Q.card := lt_of_lt_of_le (by positivity) hQℓ
  have hsc : ((p.length : ℕ) : ℝ) + Real.logb 2 (Q.card : ℕ) ≤ ((K + τ : ℕ) : ℝ) := by
    have e : setC V Q = (p.length : ℝ) := by rw [hlen]; rfl
    push_cast
    linarith
  obtain ⟨hmul, hle⟩ := card_mul_two_pow_le_of_logb hQpos hsc
  obtain ⟨c, rfl, hc⟩ := exists_shortlexWord p
  obtain ⟨s, hs⟩ := conditionalRunOut_complete hcV hp
  have hcN : c < (hammingSources cV cT K S τ).numSet := by
    change c < 2 ^ (K + τ + 1) - 1
    have : 2 ^ ((shortlexWord c).length + 1) ≤ 2 ^ (K + τ + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hs' : (hammingSources cV cT K S τ).setEval c s = some Q := by
    change (conditionalRunOut cV s (shortlexWord c) []).map decodeModel = some Q
    rw [hs, Option.map_some, decodeModel_canonicalFiniteSetCode]
  have helig : SetEligible (hammingGame M R ℓ δ) K τ Q
      ((hammingSources cV cT K S τ).setCost c) := by
    refine ⟨fun y hy => ?_, hle, hQℓ, hmul⟩
    change y ∈ (allStrings M).toFinset
    rw [List.mem_toFinset, mem_allStrings]
    exact hQM y hy
  obtain ⟨t, ht⟩ := set_mem_eventHistory (hammingGame M R ℓ δ) K τ (hammingSources cV cT K S τ)
    (fun c' s' t' Q' hst h => by
      change (conditionalRunOut cV s' (shortlexWord c') []).map decodeModel = some Q' at h
      change (conditionalRunOut cV t' (shortlexWord c') []).map decodeModel = some Q'
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [conditionalRunOut_mono cV hst hw]
      rfl) hcN hs' helig
  exact ⟨t, _, ht⟩

/-- **A common stage for finitely many eventually available evaluations**: if every member of a
list has a stage at which a stage-monotone evaluation is available, one stage (the maximum)
serves them all.
Reference: blueprint L21 ("the maximum of this finite family exists"). -/
theorem exists_common_stage {β γ : Type*} (l : List β) (f : β → ℕ → Option γ)
    (out : β → γ) (hmono : ∀ b s t, s ≤ t → f b s = some (out b) → f b t = some (out b))
    (h : ∀ b ∈ l, ∃ s, f b s = some (out b)) : ∃ s, ∀ b ∈ l, f b s = some (out b) := by
  induction l with
  | nil => exact ⟨0, fun b hb => by simp at hb⟩
  | cons a l ih =>
    obtain ⟨s₁, hs₁⟩ := h a (by simp)
    obtain ⟨s₂, hs₂⟩ := ih fun b hb => h b (by simp [hb])
    refine ⟨max s₁ s₂, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb'
    · exact hmono _ _ _ (le_max_left _ _) hs₁
    · exact hmono _ _ _ (le_max_right _ _) (hs₂ b hb')

/-- **Completeness for exact partition programs**: for a program `p` of length at most `S` which
is an exact partition program of the `M`-cube for the total interpreter, a table event `P`
eventually arrives whose cells include the cell printed by `p` at every cube point.  The program
is a shortlex candidate of index `< 2^(S+1) - 1`; all its finitely many evaluations on the cube
become available at a common stage (`exists_common_stage`); the decoded outputs pass the
partition test; apply `table_mem_eventHistory`.  Outputs are unique (`Part.mem_unique`) and the
canonical code is injective, so every printed cell is a cell of `P`. -/
theorem table_event_of_partition {cT : Nat.Partrec.Code}
    (hcT : IsCodeFor cT universalDecompressor) (cV : Nat.Partrec.Code) (M R K S τ ℓ δ : ℕ)
    {p : BitString} (hpS : p.length ≤ S) (hp : IsCubePartitionProgram M p) :
    ∃ t P, ResEvent.table P ∈
        eventHistory (hammingGame M R ℓ δ) K τ (hammingSources cV cT K S τ) t ∧
      ∀ u : BitString, u.length = M → ∀ Q : Finset BitString,
        produces universalDecompressor p u (canonicalFiniteSetCode Q) → Q ∈ P := by
  classical
  choose cell hcell using hp
  let out : BitString → Finset BitString := fun u =>
    if hu : u.length = M then cell u hu else ∅
  have hout : ∀ u (hu : u.length = M), out u = cell u hu := fun u hu => by
    simp [out, hu]
  obtain ⟨c, rfl, hc⟩ := exists_shortlexWord p
  have hcN : c < (hammingSources cV cT K S τ).numTab := by
    change c < 2 ^ (S + 1) - 1
    have : 2 ^ ((shortlexWord c).length + 1) ≤ 2 ^ (S + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hmono : ∀ u s t, s ≤ t →
      (hammingSources cV cT K S τ).tabEval c u s = some (out u) →
      (hammingSources cV cT K S τ).tabEval c u t = some (out u) := by
    intro u s t hst h
    change (conditionalRunOut cT s (shortlexWord c) u).map decodeModel = some (out u) at h
    change (conditionalRunOut cT t (shortlexWord c) u).map decodeModel = some (out u)
    obtain ⟨w, hw, hw'⟩ := Option.map_eq_some_iff.mp h
    rw [conditionalRunOut_mono cT hst hw, Option.map_some, hw']
  have havail : ∀ u ∈ (hammingGame M R ℓ δ).centers,
      ∃ s, (hammingSources cV cT K S τ).tabEval c u s = some (out u) := by
    intro u hu
    have hu' : u.length = M := (mem_allStrings M u).1 hu
    obtain ⟨s, hs⟩ := conditionalRunOut_complete hcT (hcell u hu').1
    refine ⟨s, ?_⟩
    change (conditionalRunOut cT s (shortlexWord c) u).map decodeModel = some (out u)
    rw [hs, Option.map_some, decodeModel_canonicalFiniteSetCode, hout u hu']
  obtain ⟨s, hs⟩ := exists_common_stage _ (fun u => (hammingSources cV cT K S τ).tabEval c u)
    out hmono havail
  have hvalid : ∀ u ∈ (hammingGame M R ℓ δ).centers, out u ⊆ (hammingGame M R ℓ δ).cube ∧
      u ∈ out u ∧ ∀ v ∈ out u, out v = out u := by
    intro u hu
    have hu' : u.length = M := (mem_allStrings M u).1 hu
    obtain ⟨hprod, hmem, hall⟩ := hcell u hu'
    rw [hout u hu']
    refine ⟨fun y hy => ?_, hmem, fun v hv => ?_⟩
    · change y ∈ (allStrings M).toFinset
      rw [List.mem_toFinset, mem_allStrings]
      exact (hall y hy).1
    · obtain ⟨hvM, hvprod⟩ := hall v hv
      rw [hout v hvM]
      exact canonicalFiniteSetCode_injective
        (Part.mem_unique (hcell v hvM).1 hvprod)
  obtain ⟨t, ht⟩ := table_mem_eventHistory (hammingGame M R ℓ δ) K τ
    (hammingSources cV cT K S τ) (fun c' u s' t' Q' hst h => by
      change (conditionalRunOut cT s' (shortlexWord c') u).map decodeModel = some Q' at h
      change (conditionalRunOut cT t' (shortlexWord c') u).map decodeModel = some Q'
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [conditionalRunOut_mono cT hst hw]
      rfl) hcN hs hvalid
  refine ⟨t, _, ht, fun u hu Q hQ => ?_⟩
  have hQ' : Q = out u := by
    rw [hout u hu]
    exact canonicalFiniteSetCode_injective (Part.mem_unique hQ (hcell u hu).1)
  rw [hQ']
  exact List.mem_map.2 ⟨u, (mem_allStrings M u).2 hu, rfl⟩

/-! ### The natural-number image and the emitted centers -/

/-- The point embedding of words into naturals, by their `Encodable` codes. -/
def wordEmb : BitString ↪ ℕ :=
  ⟨Encodable.encode, Encodable.encode_injective⟩

/-- Decoding a natural to a word (the empty word on non-codes). -/
def natWord (n : ℕ) : BitString :=
  (Encodable.decode n).getD []

/-- `natWord` inverts the embedding. -/
theorem natWord_wordEmb (u : BitString) : natWord (wordEmb u) = u := by
  simp [natWord, wordEmb]

/-- The natural-number image of the Hamming game (the computable form of `hammingGame`). -/
def hammingGameNat (M R ℓ δ : ℕ) : ResGame ℕ where
  centers := (allStrings M).map wordEmb
  sphere n := (hammingSphere (natWord n).length (natWord n) R).map wordEmb
  N := M.choose R
  ell := ℓ
  delta := δ
  fallback := wordEmb (List.replicate M false)

/-- The natural-number image of the Hamming event sources. -/
noncomputable def hammingSourcesNat (cV cT : Nat.Partrec.Code) (K S τ : ℕ) : EventSources ℕ where
  numPt := 2 ^ K - 1
  ptEval c s := (conditionalRunOut cV s (shortlexWord c) []).map wordEmb
  numSet := 2 ^ (K + τ + 1) - 1
  setEval c s := (conditionalRunOut cV s (shortlexWord c) []).map fun w =>
    (decodeModel w).map wordEmb
  setCost c := (shortlexWord c).length
  numTab := 2 ^ (S + 1) - 1
  tabEval c n s := (conditionalRunOut cT s (shortlexWord c) (natWord n)).map fun w =>
    (decodeModel w).map wordEmb

/-- **The natural-number game is the image of the Hamming game** (`natWord_wordEmb` for the
spheres).
Reference: `ReservoirTransport.IsGameImage`; blueprint L22. -/
theorem hammingGame_image (M R ℓ δ : ℕ) :
    IsGameImage wordEmb (hammingGame M R ℓ δ) (hammingGameNat M R ℓ δ) where
  centers := rfl
  sphere z := by
    change (hammingSphere (natWord (wordEmb z)).length (natWord (wordEmb z)) R).map wordEmb =
      (hammingSphere z.length z R).map wordEmb
    rw [natWord_wordEmb]
  N := rfl
  ell := rfl
  delta := rfl
  fallback := rfl

/-- **The natural-number sources are the image of the Hamming sources** (`Option.map_map`,
`natWord_wordEmb`).
Reference: `ReservoirTransport.IsSourceImage`; blueprint L22. -/
theorem hammingSources_image (cV cT : Nat.Partrec.Code) (K S τ : ℕ) :
    IsSourceImage wordEmb (hammingSources cV cT K S τ) (hammingSourcesNat cV cT K S τ) where
  numPt := rfl
  ptEval _ _ := rfl
  numSet := rfl
  setEval c s := (Option.map_map (Finset.map wordEmb) decodeModel _).symm
  setCost _ := rfl
  numTab := rfl
  tabEval c u s := by
    change (conditionalRunOut cT s (shortlexWord c) (natWord (wordEmb u))).map
        (fun w => (decodeModel w).map wordEmb) =
      ((conditionalRunOut cT s (shortlexWord c) u).map decodeModel).map (Finset.map wordEmb)
    rw [natWord_wordEmb]
    exact (Option.map_map (Finset.map wordEmb) decodeModel _).symm

/-- The parameter list `[M, R, K, S, τ, ℓ, δ, h]` read off a list of naturals. -/
def hammingGameOf (ps : List ℕ) : ResGame ℕ :=
  hammingGameNat (ps.getD 0 0) (ps.getD 1 0) (ps.getD 5 0) (ps.getD 6 0)

/-- The natural-number sources of a parameter list `[M, R, K, S, τ, ℓ, δ, h]`. -/
noncomputable def hammingSourcesOf (cV cT : Nat.Partrec.Code) (ps : List ℕ) : EventSources ℕ :=
  hammingSourcesNat cV cT (ps.getD 2 0) (ps.getD 3 0) (ps.getD 4 0)

/-- The image of a sphere under `wordEmb` is the finite set of the codes of its sphere list. -/
theorem hammingSphere_map_wordEmb (R : ℕ) (z : BitString) :
    (hammingSphere z.length z R).map wordEmb =
      ((sphereList R z).map Encodable.encode).toFinset := by
  ext x
  simp only [Finset.mem_map, List.mem_toFinset, List.mem_map, mem_sphereList_iff]
  rfl

/-- The image of a decoded model under `wordEmb` is the finite set of the codes of its points. -/
theorem decodeModel_map_wordEmb (w : BitString) :
    (decodeModel w).map wordEmb =
      ((canonicalPointListOfCode w).map Encodable.encode).toFinset := by
  ext x
  simp only [decodeModel, Finset.mem_map, List.mem_toFinset, List.mem_map]
  rfl

/-- The point embedding `wordEmb` is computable. -/
theorem wordEmb_computable : Computable (wordEmb : BitString → ℕ) :=
  Computable.encode.of_eq fun _ => rfl

/-- Decoding naturals to words is computable. -/
theorem natWord_computable : Computable natWord :=
  Computable.option_getD Computable.decode (Computable.const [])

/-- Reading a fixed entry of a parameter list is computable. -/
theorem getD_computable (i : ℕ) : Computable fun ps : List ℕ => ps.getD i 0 :=
  (Primrec.list_getD 0).to_comp.comp Computable.id (Computable.const i)

/-- **The natural-number Hamming games are computable in the parameter list**: the centers are
codes of `allStrings M`, the sphere of a code is the finite set of the codes of a sphere list
(`hammingSphere_map_wordEmb`), and `N = (M choose R)` is the length of a sphere list around the
zero word (`length_sphereList`).
Reference: blueprint L22 ("simulate the deterministic event process"). -/
theorem hammingGameOf_computable : IsComputableGame hammingGameOf := by
  have hrep : Computable fun ps : List ℕ => List.replicate (ps.getD 0 0) false :=
    ((Primrec.list_map Primrec.list_range (Primrec.const false).to₂).to_comp.comp
      (getD_computable 0)).of_eq fun ps => by simp
  refine ⟨?_, ?_, ?_, getD_computable 5, getD_computable 6, wordEmb_computable.comp hrep⟩
  · exact (Computable.list_map
      (CodedFiniteDistribution.allStrings_primrec.to_comp.comp (getD_computable 0))
      (wordEmb_computable.comp Computable.snd).to₂).of_eq fun _ => rfl
  · exact (computable_listToFinset.comp (Computable.list_map
      (sphereList_primrec.to_comp.comp ((getD_computable 1).comp Computable.fst)
        (natWord_computable.comp Computable.snd))
      (Computable.encode.comp Computable.snd).to₂)).of_eq
      fun x => (hammingSphere_map_wordEmb _ _).symm
  · refine (Computable.list_length.comp
      (sphereList_primrec.to_comp.comp (getD_computable 1) hrep)).of_eq fun ps => ?_
    change _ = (ps.getD 0 0).choose (ps.getD 1 0)
    rw [length_sphereList, List.length_replicate]

/-- **The natural-number Hamming sources are computable in the parameter list**: the counts are
powers of two minus one, the evaluators are the bounded evaluators `conditionalRunOut` (node L04)
on shortlex programs, and decoded models are mapped to finite sets of codes
(`decodeModel_map_wordEmb`, `computable_listToFinset`).
Reference: blueprint L14 ("bounded evaluators"), L22. -/
theorem hammingSourcesOf_computable (cV cT : Nat.Partrec.Code) :
    IsComputableSources (hammingSourcesOf cV cT) := by
  have hpow : Primrec₂ fun a b : ℕ => a ^ b := Primrec.nat_iff.mpr Nat.Primrec.pow
  have htwo : ∀ {f : List ℕ → ℕ}, Computable f → Computable fun ps => 2 ^ f ps - 1 :=
    fun hf => Primrec.nat_sub.to_comp.comp (hpow.to_comp.comp (Computable.const 2) hf)
      (Computable.const 1)
  have hmodel : Computable fun w : BitString => (decodeModel w).map wordEmb :=
    (computable_listToFinset.comp (Computable.list_map canonicalPointListOfCode_computable
      (Computable.encode.comp Computable.snd).to₂)).of_eq
      fun w => (decodeModel_map_wordEmb w).symm
  have hrunV : Computable fun x : List ℕ × ℕ × ℕ =>
      conditionalRunOut cV x.2.2 (shortlexWord x.2.1) [] :=
    (conditionalRunOut_computable cV).comp ((Computable.snd.comp Computable.snd).pair
      ((shortlexWord_computable.comp (Computable.fst.comp Computable.snd)).pair
        (Computable.const [])))
  have hrunT : Computable fun x : List ℕ × ℕ × ℕ × ℕ =>
      conditionalRunOut cT x.2.2.2 (shortlexWord x.2.1) (natWord x.2.2.1) :=
    (conditionalRunOut_computable cT).comp
      ((Computable.snd.comp (Computable.snd.comp Computable.snd)).pair
      ((shortlexWord_computable.comp (Computable.fst.comp Computable.snd)).pair
        (natWord_computable.comp (Computable.fst.comp (Computable.snd.comp Computable.snd)))))
  refine ⟨htwo (getD_computable 2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Computable.option_map hrunV (wordEmb_computable.comp Computable.snd).to₂).of_eq
      fun _ => rfl
  · exact (htwo (Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp (getD_computable 2)
      (getD_computable 4)) (Computable.const 1))).of_eq fun _ => rfl
  · exact (Computable.option_map hrunV (hmodel.comp Computable.snd).to₂).of_eq fun _ => rfl
  · exact (Computable.list_length.comp (shortlexWord_computable.comp Computable.snd)).of_eq
      fun _ => rfl
  · exact (htwo (Primrec.nat_add.to_comp.comp (getD_computable 3) (Computable.const 1))).of_eq
      fun _ => rfl
  · exact (Computable.option_map hrunT (hmodel.comp Computable.snd).to₂).of_eq fun _ => rfl

/-- **The stream of emitted centers** of the Hamming game for the parameter list
`ps = [M, R, K, S, τ, ℓ, δ, h]` at stage `s`, computed through the natural-number image and
decoded back to words. -/
noncomputable def hammingEmit (cV cT : Nat.Partrec.Code) (ps : List ℕ) (s : ℕ) :
    List BitString :=
  (emittedCenters (hammingGameOf ps)
    (eventHistory (hammingGameOf ps) (ps.getD 2 0) (ps.getD 4 0) (hammingSourcesOf cV cT ps)
      s)).map natWord

/-- **The emitted-center stream is computable** (`emittedCenters_eventHistory_computable` for the
natural-number image, then decoding by `natWord`). -/
theorem hammingEmit_computable (cV cT : Nat.Partrec.Code) :
    Computable₂ (hammingEmit cV cT) := by
  have hK : Computable fun ps : List ℕ => ps.getD 2 0 :=
    (Primrec.list_getD 0).to_comp.comp Computable.id (Computable.const 2)
  have hτ : Computable fun ps : List ℕ => ps.getD 4 0 :=
    (Primrec.list_getD 0).to_comp.comp Computable.id (Computable.const 4)
  have h := emittedCenters_eventHistory_computable hammingGameOf_computable
    (hammingSourcesOf_computable cV cT) hK hτ
  have hdec : Computable natWord :=
    Computable.option_getD Computable.decode (Computable.const [])
  exact (Computable.list_map h (hdec.comp Computable.snd).to₂).of_eq fun _ => rfl

/-- **The emitted-center stream grows by appending** (`eventHistory_prefix`,
`emittedCenters_prefix`). -/
theorem hammingEmit_mono (cV cT : Nat.Partrec.Code) (ps : List ℕ) (s : ℕ) :
    hammingEmit cV cT ps s <+: hammingEmit cV cT ps (s + 1) :=
  ((emittedCenters_prefix _ (eventHistory_prefix _ _ _ _ (Nat.le_succ s))).map natWord)

/-- **The stream is the emitted centers of the Hamming game**: for the parameter list
`[M, R, K, S, τ, ℓ, δ, h]`, `hammingEmit` is the list of centers emitted by `hammingGame` along its
own event history (transport along `wordEmb`: `eventHistory_map`, `emittedCenters_map`,
`natWord_wordEmb`). -/
theorem hammingEmit_eq (cV cT : Nat.Partrec.Code) (M R K S τ ℓ δ h s : ℕ) :
    hammingEmit cV cT [M, R, K, S, τ, ℓ, δ, h] s =
      emittedCenters (hammingGame M R ℓ δ)
        (eventHistory (hammingGame M R ℓ δ) K τ (hammingSources cV cT K S τ) s) := by
  have hG := hammingGame_image M R ℓ δ
  have hsrc := hammingSources_image cV cT K S τ
  have e1 : hammingEmit cV cT [M, R, K, S, τ, ℓ, δ, h] s =
      (emittedCenters (hammingGameNat M R ℓ δ)
        (eventHistory (hammingGameNat M R ℓ δ) K τ (hammingSourcesNat cV cT K S τ) s)).map
          natWord :=
    rfl
  rw [e1, eventHistory_map hG hsrc, emittedCenters_map hG, List.map_map]
  conv_rhs => rw [← List.map_id (emittedCenters _ _)]
  exact List.map_congr_left fun u _ => natWord_wordEmb u

end Kolmogorov.StrongMerging.Lower
