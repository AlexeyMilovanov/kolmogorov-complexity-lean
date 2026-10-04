import KolmogorovMathlib.StoppingComplexity.StrategyComputable

/-!
# The word-answer game and the shadow of a local strategy

Blueprint part 02, §7 (LEM-SHADOW: padding word responses) and part 03, §6 (the interface
exported by the game proof). In the game `G_b` played against the universal machine, Bob's
answer to a request `(x, n)` is a *word* of length at most `b n` (a witness of the machine),
prefix-incomparable with the answers at distinct comparable vertices; Alice wins when every
reachable history leads to a fresh request with a positive exponent, keeps every path load at
most `1`, and the play ends within `T` requests. A local strategy of the dyadic game is
*shadowed* into this game by reading each word, padded with zeros to `d + cap` bits, as the
address of a depth-`d` cell of the board `[0, 2^cap)` (`wordToCell`); the bridge lemma
`reachable_of_reachableWordHistory` turns a word-reachable history of the shadow into a
reachable history of the local strategy (through it the exponent and height bounds of
LEM-EFF-01 reach the word game: W1/W2), and LEM-SHADOW is the winning transfer. Both
conventions of the blueprint are one definition: `cap = 0` (pad to `n + f(n) + c`, board
`[0, 1)`, T3c) and `cap = c` (the palette `[0, 2^c)`, T3).
-/

namespace Kolmogorov

/-! ### The word-answer game (03 §6, items 2–5) -/

/-- A history of the word game: requests with Bob's word answers. Blueprint 03 §6. -/
abbrev WordHistory := List (Request × BitString)

/-- A strategy of the word game. Blueprint 03 §6. -/
abbrev WordStrategy := WordHistory → Request

/-- Bob's reply `p` to the request `r` after the history `h` in `G_b` is legal when it has at
most `b n` bits (`n` the exponent of `r`) and is prefix-incomparable with the replies at
distinct vertices comparable with the vertex of `r`. Blueprint 03 §6. -/
def LegalWordAnswer (b : ℕ → ℕ) (h : WordHistory) (r : Request) (p : BitString) : Prop :=
  p.length ≤ b r.2 ∧ ∀ e ∈ h, IsComparable e.1.1 r.1 → e.1.1 ≠ r.1 → IsIncomparable e.2 p

/-- The histories of `G_b` reachable by playing `σ` against legal word answers.
Blueprint 03 §6. -/
inductive ReachableWordHistory (b : ℕ → ℕ) (σ : WordStrategy) : WordHistory → Prop
  /-- The empty history is reachable. -/
  | nil : ReachableWordHistory b σ []
  /-- A legal word answer to the current request extends a reachable history. -/
  | snoc {h : WordHistory} {p : BitString} (hh : ReachableWordHistory b σ h)
      (hp : LegalWordAnswer b h (σ h) p) : ReachableWordHistory b σ (h ++ [(σ h, p)])

/-- Items 2–5 of the interface of 03 §6 for one tag: at every reachable history the next
request has exponent `≥ 1`, its vertex is fresh, the path loads including the pending request
are at most `1`, and the play is within `T` requests (item 1, computability, is a separate
hypothesis of the diagonalization theorem). Blueprint 03 §6. -/
def IsWinningWordStrategy (b : ℕ → ℕ) (T : ℕ) (σ : WordStrategy) : Prop :=
  ∀ h, ReachableWordHistory b σ h →
    1 ≤ (σ h).2 ∧ (σ h).1 ∉ h.map (fun e => e.1.1) ∧
      HasBudget (h.map Prod.fst ++ [σ h]) 1 ∧ h.length + 1 ≤ T

/-- A family of winning word strategies, one per tag `c`, with per-tag length bounds `b c`
and per-tag request bounds `T c`. Blueprint 03 §6. -/
def IsWinningWordFamily (b : ℕ → ℕ → ℕ) (σ : ℕ → WordStrategy) (T : ℕ → ℕ) : Prop :=
  ∀ c, IsWinningWordStrategy (b c) (T c) (σ c)

/-! ### Shadowing a local strategy (LEM-SHADOW) -/

/-- Read a word answer as a cell: pad `p` with zeros to `d + cap` bits and take the address of
the depth-`d` cell of the board `[0, 2^cap)` it denotes. Blueprint 02 LEM-SHADOW. -/
def wordToCell (cap d : ℕ) (p : BitString) : DyadicCell :=
  cellOfAddress cap (padZeros (d + cap) p)

/-- The shadow of a local strategy in the word game: every word answer at exponent `n` is read
as a cell of the depth `depthOf n`. Blueprint 02 LEM-SHADOW. -/
def wordStrategyOfLocal (cap : ℕ) (depthOf : ℕ → ℕ) (σ : LocalStrategy) : WordStrategy :=
  fun h => σ (h.map fun e => (e.1, wordToCell cap (depthOf e.1.2) e.2))

/-- Padding to `len` bits leaves at least `len` bits. Blueprint 01 F1-CODE. -/
private theorem le_length_padZeros (len : ℕ) (p : BitString) :
    len ≤ (padZeros len p).length := by
  simp only [padZeros, List.length_append, List.length_replicate]
  omega

/-- A word of length at least `cap` is the address of the cell it addresses: the address has
`(|w| - cap) + cap = |w|` bits and the value `natOfBits w`, and re-encoding the value of a word
in its own length returns the word. Blueprint 01 F1-CELL. -/
private theorem cellAddress_cellOfAddress {cap : ℕ} {w : BitString} (h : cap ≤ w.length) :
    cellAddress cap (cellOfAddress cap w) = w := by
  simp only [cellAddress, cellOfAddress, Nat.sub_add_cancel h]
  exact bitsOfNatBE_natOfBits w

/-- Incomparable word answers are read as disjoint cells, whatever the two depths: the padded
words stay incomparable (the disagreeing position lies in both original words), they are the
addresses of the two cells, and inside `[0, 2^cap)` disjointness of cells is incomparability of
their addresses. Blueprint 02 LEM-SHADOW. -/
private theorem cellsDisjoint_wordToCell {cap d d' : ℕ} {p q : BitString}
    (h : IsIncomparable p q) : CellsDisjoint (wordToCell cap d p) (wordToCell cap d' q) := by
  have hp : cap ≤ (padZeros (d + cap) p).length :=
    (Nat.le_add_left cap d).trans (le_length_padZeros _ p)
  have hq : cap ≤ (padZeros (d' + cap) q).length :=
    (Nat.le_add_left cap d').trans (le_length_padZeros _ q)
  rw [wordToCell, wordToCell, cellsDisjoint_iff_isIncomparable_cellAddress
    (cellInCapacity_cellOfAddress hp) (cellInCapacity_cellOfAddress hq),
    cellAddress_cellOfAddress hp, cellAddress_cellOfAddress hq]
  exact isIncomparable_padZeros h _ _

/-- LEM-SHADOW for one answer: a legal word answer `p` to `r` with the length bound
`b r.2 = δ(r.2) + cap`, read as the cell `wordToCell cap δ(r.2) p`, is a legal local answer in
capacity `2^cap` after the history read in the same way: the padded word has exactly
`δ(r.2) + cap` bits, so the cell has the prescribed depth `δ(r.2)` and lies in `[0, 2^cap)`, and
incomparable replies at distinct comparable vertices become disjoint cells.
Blueprint 02 LEM-SHADOW. -/
private theorem legalAnswer_wordToCell {S : GameSchedule} {cap : ℕ} {b : ℕ → ℕ}
    {h : WordHistory} {r : Request} {p : BitString} (hb : b r.2 = S.depthOfExp r.2 + cap)
    (hp : LegalWordAnswer b h r p) :
    LegalAnswer S (2 ^ cap) (h.map fun e => (e.1, wordToCell cap (S.depthOfExp e.1.2) e.2)) r
      (wordToCell cap (S.depthOfExp r.2) p) := by
  obtain ⟨hlen, hinc⟩ := hp
  refine ⟨?_, cellInCapacity_cellOfAddress
    ((Nat.le_add_left cap _).trans (le_length_padZeros _ p)), ?_⟩
  · rw [wordToCell, depth_cellOfAddress, length_padZeros (hb ▸ hlen), Nat.add_sub_cancel]
  · intro e he hcomp hne
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    exact cellsDisjoint_wordToCell (hinc e' he' hcomp hne)

/-- The word→local bridge (W1/W2): a word-reachable history of the shadow of `σ`, once its
answers are read as cells, is a reachable history of `σ` in the local game of capacity
`2^cap`; through it `RequestAllowed` (exponents `≤ E_R`) and the height bound of LEM-EFF-01
reach the word game. Blueprint 02 LEM-SHADOW / 04 W1–W2. -/
theorem reachable_of_reachableWordHistory {S : GameSchedule} {cap T : ℕ} {σ : LocalStrategy}
    {b : ℕ → ℕ} (hS : S.IsValid) (hσ : IsWinningLocalStrategy S S.R (2 ^ cap) 1 T σ)
    (hb : ∀ n ∈ S.exps, b n = S.depthOfExp n + cap) {h : WordHistory}
    (hh : ReachableWordHistory b (wordStrategyOfLocal cap S.depthOfExp σ) h) :
    Reachable S (2 ^ cap) σ (h.map fun e => (e.1, wordToCell cap (S.depthOfExp e.1.2) e.2)) := by
  have _ := hS
  induction hh with
  | nil => exact ReachableFrom.nil
  | @snoc h p hh hp ih =>
    have hmem := List.mem_of_mem_take (hσ _ ih).2.1
    rw [List.map_append, List.map_singleton]
    exact ReachableFrom.snoc ih (legalAnswer_wordToCell (hb _ hmem) hp)

/-- **LEM-SHADOW.** If `σ` wins the local game of capacity `2^cap` with budget `1` and request
bound `T` for a valid schedule, and the word lengths are `b n = δ(n) + cap` on the exponents of
the schedule, then the shadow of `σ` wins `G_b` within `T` requests. Validity of the schedule
supplies DEF-01's `n ≥ 1` (`E_0 ≥ 1`, strictly increasing exponents). Blueprint 02 LEM-SHADOW. -/
theorem wordStrategyOfLocal_winning {S : GameSchedule} {cap T : ℕ} {σ : LocalStrategy}
    {b : ℕ → ℕ} (hS : S.IsValid) (hσ : IsWinningLocalStrategy S S.R (2 ^ cap) 1 T σ)
    (hb : ∀ n ∈ S.exps, b n = S.depthOfExp n + cap) :
    IsWinningWordStrategy b T (wordStrategyOfLocal cap S.depthOfExp σ) := by
  intro h hh
  obtain ⟨hnew, hallowed, hbudget, hlen⟩ :=
    hσ _ (reachable_of_reachableWordHistory hS hσ hb hh)
  simp only [requestsOf, List.nil_append, List.map_map, List.length_map] at hnew hbudget hlen
  exact ⟨GameSchedule.one_le_of_requestAllowed hS hallowed, hnew, hbudget, hlen⟩

/-- Reading a word answer as a cell is primitive recursive in the capacity, the depth and the
word: the zero padding is an `append` of a `replicate`, and the cell is the padded length minus
the capacity together with the big-endian value. Blueprint 02 LEM-SHADOW / LEM-EFF-02. -/
private theorem primrec_wordToCell :
    Primrec fun a : ℕ × ℕ × BitString => wordToCell a.1 a.2.1 a.2.2 := by
  have hpad : Primrec fun a : ℕ × ℕ × BitString => padZeros (a.2.1 + a.1) a.2.2 :=
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.list_replicate.comp
        (Primrec.nat_sub.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
          (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.const false))).of_eq fun _ => rfl
  exact ((Primrec.nat_sub.comp (Primrec.list_length.comp hpad) Primrec.fst).pair
    (primrec_natOfBits.comp hpad)).of_eq fun _ => rfl

/-- The depth prescribed for an exponent is primitive recursive in the schedule and the
exponent: the position of the exponent in the exponent list, read in the depth list.
Blueprint 02 DEF-03 / LEM-EFF-02. -/
private theorem primrec_depthOfExp : Primrec₂ GameSchedule.depthOfExp := by
  have hexps : Primrec GameSchedule.exps :=
    (Primrec.fst.comp (Primrec.of_equiv (e := GameSchedule.equivProd))).of_eq fun _ => rfl
  have hdepths : Primrec GameSchedule.depths :=
    (Primrec.snd.comp (Primrec.of_equiv (e := GameSchedule.equivProd))).of_eq fun _ => rfl
  exact ((Primrec.list_getD 0).comp (hdepths.comp Primrec.fst)
    (Primrec.list_idxOf.comp Primrec.snd (hexps.comp Primrec.fst))).of_eq fun _ => rfl

/-- Computability of the shadow of the strategy of `Strategy`, uniformly in the palette size,
the schedule, the level and the capacity (item 1 of 03 §6 for the constructed families).
Blueprint 02 LEM-SHADOW / 03 §6. -/
theorem wordStrategyOfLocal_computable :
    Computable fun a : ℕ × GameSchedule × ℕ × ℚ × WordHistory =>
      wordStrategyOfLocal a.1 a.2.1.depthOfExp (localStrategy a.2.1 a.2.2.1 a.2.2.2.1)
        a.2.2.2.2 := by
  have hcell : Primrec₂ fun (a : ℕ × GameSchedule × ℕ × ℚ × WordHistory)
      (e : Request × BitString) => (e.1, wordToCell a.1 (a.2.1.depthOfExp e.1.2) e.2) :=
    Primrec₂.mk ((Primrec.fst.comp Primrec.snd).pair (primrec_wordToCell.comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((primrec_depthOfExp.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))).pair
          (Primrec.snd.comp Primrec.snd)))))
  have hmap : Primrec fun a : ℕ × GameSchedule × ℕ × ℚ × WordHistory =>
      a.2.2.2.2.map fun e => (e.1, wordToCell a.1 (a.2.1.depthOfExp e.1.2) e.2) :=
    Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) hcell
  exact (localStrategy_computable.comp ((Computable.fst.comp Computable.snd).pair
    ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
      ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))).pair
        hmap.to_comp)))).of_eq fun _ => rfl

end Kolmogorov
