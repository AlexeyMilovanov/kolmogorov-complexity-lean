/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.MultiheadAutomata.AutomatonDefs

/-!
# Head Hierarchy

Head hierarchy for multihead finite automata (Shen–Uspensky–Vereshchagin, Theorem 154): for every
`k` there is a language recognized by a `(k + 1)`-head automaton and not by any `k`-head one.

The separating languages are the palindrome-block languages `L_m`, consisting of the words
`w_1 # … # w_m # w_m # … # w_1` over blocks of bits, with `m = (k + 1) k / 2`.  The proof is by
Kolmogorov-style counting: a `k`-head automaton with finitely many states cannot compare all `m`
pairs of blocks, since some block is not visited by a pair of heads; a pigeonhole argument then
gives two different tuples of blocks with the same configurations, and cutting and pasting the
accepting run makes the automaton accept a word outside `L_m`.

The main declaration is `exists_language_isRecognizedBy_succ_not` (Theorem 154); the private
lemmas carry out the individual steps of this argument.
-/

namespace Kolmogorov.Applications

/-- The word `w_1 # … # w_m # w'_m # … # w'_1` of two tuples of blocks.  `mixedWord w w` is the
typical element of `L_m`; `mixedWord w w'` is not in `L_m` when `w ≠ w'`. -/
private def mixedWord {m : ℕ} (w w' : Fin m → List Bool) : List BlockSymbol :=
  blockWord (List.ofFn w ++ (List.ofFn w').reverse)

/-- `blockWord` of a single block is the encoding of this block. -/
private lemma not_isRecognizedBy_palindromeBlocks_aux_blockWord_singleton (a : List Bool) :
    blockWord [a] = a.map BlockSymbol.bit := by
  simp [blockWord]

/-- `blockWord` of at least two blocks: the first block, a separator, and the rest. -/
private lemma not_isRecognizedBy_palindromeBlocks_aux_blockWord_cons_cons (a b : List Bool)
    (t : List (List Bool)) :
    blockWord (a :: b :: t) = a.map BlockSymbol.bit ++ BlockSymbol.sep :: blockWord (b :: t) := by
  simp [blockWord, List.intercalate]

/-- Cutting at the first separator: if two words without separator in the prefix are equal after
appending `sep :: y`, resp. `sep :: y'`, then both parts coincide. -/
private lemma not_isRecognizedBy_palindromeBlocks_aux_split_sep (x x' y y' : List BlockSymbol)
    (hx : BlockSymbol.sep ∉ x) (hx' : BlockSymbol.sep ∉ x')
    (h : x ++ BlockSymbol.sep :: y = x' ++ BlockSymbol.sep :: y') : x = x' ∧ y = y' := by
  induction x generalizing x' with
  | nil =>
    cases x' with
    | nil => simpa using h
    | cons c x'' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hx'
  | cons c x ih =>
    cases x' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hx
    | cons c' x'' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      have := ih x'' (fun hm => hx (List.mem_cons_of_mem _ hm))
        (fun hm => hx' (List.mem_cons_of_mem _ hm)) h2
      exact ⟨by rw [this.1], this.2⟩

/-- `blockWord` is injective on lists of blocks of the same length. -/
private lemma not_isRecognizedBy_palindromeBlocks_aux_blockWord_inj :
    ∀ (L L' : List (List Bool)), blockWord L = blockWord L' → L.length = L'.length → L = L' := by
  intro L
  induction L with
  | nil =>
    intro L' _ hlen
    cases L' with
    | nil => rfl
    | cons a t => simp at hlen
  | cons a t ih =>
    intro L' h hlen
    cases L' with
    | nil => simp at hlen
    | cons a' t' =>
      cases t with
      | nil =>
        cases t' with
        | nil =>
          rw [not_isRecognizedBy_palindromeBlocks_aux_blockWord_singleton,
            not_isRecognizedBy_palindromeBlocks_aux_blockWord_singleton] at h
          rw [List.map_inj_right (fun x y hxy => by simpa using hxy) |>.mp h]
        | cons b' t'' => simp at hlen
      | cons b t0 =>
        cases t' with
        | nil => simp at hlen
        | cons b' t0' =>
          rw [not_isRecognizedBy_palindromeBlocks_aux_blockWord_cons_cons,
            not_isRecognizedBy_palindromeBlocks_aux_blockWord_cons_cons] at h
          obtain ⟨h1, h2⟩ := not_isRecognizedBy_palindromeBlocks_aux_split_sep _ _ _ _
            (by simp) (by simp) h
          have h3 : a = a' := (List.map_inj_right (fun x y hxy => by simpa using hxy)).mp h1
          have h4 : b :: t0 = b' :: t0' := ih (b' :: t0') h2 (by simpa using hlen)
          rw [h3, h4]

/-- Step 1 of the proof of `not_isRecognizedBy_palindromeBlocks`: `mixedWord w w'` lies
in `L_m` exactly when the two halves coincide, `w = w'`.  (The encoding `blockWord` of a list of
blocks is injective on lists of the same length: the separators `#` cut the word back into the
blocks; here both lists have length `2 m`.) -/
private lemma not_isRecognizedBy_palindromeBlocks_inj {m : ℕ} (w w' : Fin m → List Bool) :
    mixedWord w w' ∈ palindromeBlocks m ↔ w = w' := by
  constructor
  · rintro ⟨v, hv⟩
    have hL := not_isRecognizedBy_palindromeBlocks_aux_blockWord_inj _ _ hv (by simp)
    obtain ⟨h1, h2⟩ := List.append_inj hL (by simp)
    have hwv : w = v := List.ofFn_injective h1
    have hw'v : w' = v := List.ofFn_injective (List.reverse_injective h2)
    rw [hwv, hw'v]
  · rintro rfl
    exact ⟨w, rfl⟩

/-- Step 2A of the proof of `not_isRecognizedBy_palindromeBlocks` (pair counting, the
"key observation" on p. 249 of the chapter text): let `P t a` be the position of head `a` at time
`t` (monotone in `t`), and let `I i = [I_lo i, I_hi i)` be the positions of the left copy of the
`i`-th block and `J i = [J_lo i, J_hi i)` those of the right copy; the left copies are ordered
increasingly in `i` and lie to the left of all right copies, and the right copies are ordered
decreasingly in `i`.  Call `i` *visited* if at some time one head is in `I i` and another one in
`J i`.  A pair of heads can visit at most one block (if it visited `i < j`, the head in the left
half would have to move forward and the head in the right half backward in time), and the unordered
pair `{a, b}` determines the block (a head cannot go from the right half back to the left half).
Hence at most `k.choose 2` blocks are visited. -/
private lemma not_isRecognizedBy_palindromeBlocks_step2A_pairCounting {k m : ℕ}
    (P : ℕ → Fin k → ℕ) (hmono : ∀ t a, P t a ≤ P (t + 1) a)
    (I_lo I_hi J_lo J_hi : Fin m → ℕ)
    (hI : ∀ i j : Fin m, i < j → I_hi i ≤ I_lo j)
    (hJ : ∀ i j : Fin m, i < j → J_hi j ≤ J_lo i)
    (hIJ : ∀ i j : Fin m, I_hi i ≤ J_lo j)
    (S : Finset (Fin m))
    (hS : ∀ i ∈ S, ∃ (t : ℕ) (a b : Fin k),
      I_lo i ≤ P t a ∧ P t a < I_hi i ∧ J_lo i ≤ P t b ∧ P t b < J_hi i) :
    S.card ≤ k.choose 2 := by
  -- a head that is strictly further right at time `t2` than at time `t1` is there later
  have hlt : ∀ (x : Fin k) (t1 t2 : ℕ), P t1 x < P t2 x → t1 < t2 := by
    intro x t1 t2 h
    by_contra hcon
    have hmono' : Monotone (fun t => P t x) := monotone_nat_of_le_succ (fun t => hmono t x)
    exact absurd (hmono' (not_lt.mp hcon)) (not_le.mpr h)
  choose t a b h1 h2 h3 h4 using hS
  -- the two heads of a visit are different
  have hne : ∀ (i : Fin m) (hi : i ∈ S), a i hi ≠ b i hi := by
    intro i hi hab
    have e1 := h2 i hi
    have e2 := h3 i hi
    have e3 := hIJ i i
    rw [← hab] at e2
    omega
  -- the unordered pair of heads determines the visited block
  have hinj : ∀ (i j : Fin m) (hi : i ∈ S) (hj : j ∈ S),
      ({a i hi, b i hi} : Finset (Fin k)) = {a j hj, b j hj} → i = j := by
    intro i j hi hj heq
    have heq' : ({a i hi, b i hi} : Set (Fin k)) = {a j hj, b j hj} := by
      have := congrArg (fun s : Finset (Fin k) => (s : Set (Fin k))) heq
      simpa using this
    rcases Set.pair_eq_pair_iff.mp heq' with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · by_contra hij
      rcases lt_or_gt_of_ne hij with hij' | hji'
      · have a1 := h2 i hi
        have a2 := hI i j hij'
        have a3 := h1 j hj
        have a4 := h4 j hj
        have a5 := hJ i j hij'
        have a6 := h3 i hi
        rw [← hx] at a3
        rw [← hy] at a4
        have c1 : t i hi < t j hj := hlt (a i hi) _ _ (by omega)
        have c2 : t j hj < t i hi := hlt (b i hi) _ _ (by omega)
        omega
      · have a1 := h2 j hj
        have a2 := hI j i hji'
        have a3 := h1 i hi
        have a4 := h4 i hi
        have a5 := hJ j i hji'
        have a6 := h3 j hj
        rw [← hx] at a1
        rw [← hy] at a6
        have c1 : t j hj < t i hi := hlt (a i hi) _ _ (by omega)
        have c2 : t i hi < t j hj := hlt (b i hi) _ _ (by omega)
        omega
    · exfalso
      have a1 := h2 i hi
      have a2 := hIJ i j
      have a3 := h3 j hj
      have a4 := h2 j hj
      have a5 := hIJ j i
      have a6 := h3 i hi
      rw [← hx] at a3
      rw [hy] at a6
      have c1 : t i hi < t j hj := hlt (a i hi) _ _ (by omega)
      have c2 : t j hj < t i hi := hlt (a j hj) _ _ (by omega)
      omega
  have hmaps : Set.MapsTo (fun i : {i // i ∈ S} => ({a i.1 i.2, b i.1 i.2} : Finset (Fin k)))
      (S.attach : Set {i // i ∈ S})
      ((Finset.powersetCard 2 (Finset.univ : Finset (Fin k)) : Finset (Finset (Fin k))) :
        Set (Finset (Fin k))) := by
    intro i _
    rw [Finset.mem_coe]
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair (hne i.1 i.2)⟩
  have hinj' : Set.InjOn (fun i : {i // i ∈ S} => ({a i.1 i.2, b i.1 i.2} : Finset (Fin k)))
      (S.attach : Set {i // i ∈ S}) :=
    fun i _ j _ h => Subtype.ext (hinj i.1 j.1 i.2 j.2 h)
  calc S.card = S.attach.card := Finset.card_attach.symm
    _ ≤ (Finset.powersetCard 2 (Finset.univ : Finset (Fin k))).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj'
    _ = k.choose 2 := by rw [Finset.card_powersetCard]; simp

/-- The zone of a position `p` relative to the thresholds `a ≤ b ≤ c ≤ d`: `0` before `a`, `1` in
`[a, b)` (the left copy of the block), `2` in `[b, c)`, `3` in `[c, d)` (the right copy of the
block), and `4` from `d` on. -/
private def zone (a b c d p : ℕ) : ℕ :=
  if p < a then 0 else if p < b then 1 else if p < c then 2 else if p < d then 3 else 4

/-- The *level* of a configuration: the sum over all heads of the zone of the head.  It is at most
`4 k`, and it only increases during a run. -/
private def zoneLevel {k : ℕ} (a b c d : ℕ) (pos : Fin k → ℕ) : ℕ :=
  ∑ x, zone a b c d (pos x)

/-- The first time at which the level of the run of `A` on `w` is at least `l` (the value is `0`
if there is no such time).  The configurations `A.run w (levelTime A w a b c d l)`, `l ≤ 4 k`, form
the "log file" of the run: the protocol of the moments at which a head enters or leaves a zone. -/
private noncomputable def levelTime {k : ℕ} {Sym Q : Type*} (A : MultiheadAutomaton k Sym Q)
    (w : List Sym) (a b c d l : ℕ) : ℕ :=
  sInf {t | l ≤ zoneLevel a b c d (A.run w t).pos}

/-- The case distinction on the zone of a position, for thresholds `a ≤ b ≤ c ≤ d`. -/
private lemma not_isRecognizedBy_palindromeBlocks_zone_cases {a b c d p : ℕ} (hbc : b ≤ c)
    (hcd : c ≤ d) :
    (zone a b c d p = 0 ∧ p < a) ∨ (zone a b c d p = 1 ∧ a ≤ p ∧ p < b) ∨
      (zone a b c d p = 2 ∧ b ≤ p ∧ p < c) ∨ (zone a b c d p = 3 ∧ c ≤ p ∧ p < d) ∨
      (zone a b c d p = 4 ∧ d ≤ p) := by
  unfold zone
  split_ifs <;> omega

/-- A step of `A.next` never moves a head to the left. -/
private lemma not_isRecognizedBy_palindromeBlocks_next_pos_le {k : ℕ} {Sym Q : Type*}
    (A : MultiheadAutomaton k Sym Q) (w : List Sym) (c : HeadConfig k Q) (x : Fin k) :
    c.pos x ≤ (A.next w c).pos x := by
  unfold MultiheadAutomaton.next
  split_ifs with hterm
  · exact le_rfl
  · dsimp only
    split_ifs with hmove
    · exact Nat.le_succ _
    · exact le_rfl

/-- The position of a head is monotone in time. -/
private lemma not_isRecognizedBy_palindromeBlocks_run_pos_mono {k : ℕ} {Sym Q : Type*}
    (A : MultiheadAutomaton k Sym Q) (w : List Sym) (x : Fin k) {t t' : ℕ} (htt : t ≤ t') :
    (A.run w t).pos x ≤ (A.run w t').pos x := by
  have hmono : Monotone (fun s => (A.run w s).pos x) := by
    refine monotone_nat_of_le_succ fun s => ?_
    have hrun : A.run w (s + 1) = A.next w (A.run w s) := Function.iterate_succ_apply' _ _ _
    change (A.run w s).pos x ≤ (A.run w (s + 1)).pos x
    rw [hrun]
    exact not_isRecognizedBy_palindromeBlocks_next_pos_le A w _ x
  exact hmono htt

/-- The zone is monotone in the position. -/
private lemma not_isRecognizedBy_palindromeBlocks_zone_mono {a b c d p q : ℕ} (hpq : p ≤ q) :
    zone a b c d p ≤ zone a b c d q := by
  unfold zone
  split_ifs <;> omega

/-- The zone is at most `4`. -/
private lemma not_isRecognizedBy_palindromeBlocks_zone_le_four (a b c d p : ℕ) :
    zone a b c d p ≤ 4 := by
  unfold zone
  split_ifs <;> omega

/-- The level of the run is monotone in time. -/
private lemma not_isRecognizedBy_palindromeBlocks_zoneLevel_run_mono {k : ℕ} {Sym Q : Type*}
    (A : MultiheadAutomaton k Sym Q) (w : List Sym) (a b c d : ℕ) {t t' : ℕ} (htt : t ≤ t') :
    zoneLevel a b c d (A.run w t).pos ≤ zoneLevel a b c d (A.run w t').pos := by
  unfold zoneLevel
  exact Finset.sum_le_sum fun x _ => not_isRecognizedBy_palindromeBlocks_zone_mono
    (not_isRecognizedBy_palindromeBlocks_run_pos_mono A w x htt)

/-- When the end marker is in zone `4`, every level `≤ 4 k` is reached: at the time when all heads
see the marker, the level is `4 k`. -/
private lemma not_isRecognizedBy_palindromeBlocks_exists_level {k : ℕ} {Sym Q : Type*}
    (A : MultiheadAutomaton k Sym Q) (w : List Sym) (a b c d : ℕ)
    (hd : zone a b c d w.length = 4) {l : ℕ} (hl : l ≤ 4 * k) :
    {t | l ≤ zoneLevel a b c d (A.run w t).pos}.Nonempty := by
  refine ⟨k * w.length + 1, ?_⟩
  have hterm := MultiheadAutomaton.terminated_run A w
  have h4 : ∀ i, zone a b c d ((A.run w (k * w.length + 1)).pos i) = 4 := by
    intro i
    have h1 : w[(A.run w (k * w.length + 1)).pos i]? = none := hterm i
    have h2 : w.length ≤ (A.run w (k * w.length + 1)).pos i := List.getElem?_eq_none_iff.mp h1
    have h3 := not_isRecognizedBy_palindromeBlocks_zone_mono (a := a) (b := b) (c := c) (d := d) h2
    have h5 := not_isRecognizedBy_palindromeBlocks_zone_le_four a b c d
      ((A.run w (k * w.length + 1)).pos i)
    omega
  change l ≤ zoneLevel a b c d (A.run w (k * w.length + 1)).pos
  unfold zoneLevel
  simp only [h4]
  simp
  omega

/-- The defining property of the level time: the level is reached at the level time, and not
before. -/
private lemma not_isRecognizedBy_palindromeBlocks_levelTime_spec {k : ℕ} {Sym Q : Type*}
    (A : MultiheadAutomaton k Sym Q) (w : List Sym) (a b c d : ℕ)
    (hd : zone a b c d w.length = 4) {l : ℕ} (hl : l ≤ 4 * k) :
    l ≤ zoneLevel a b c d (A.run w (levelTime A w a b c d l)).pos ∧
      ∀ t < levelTime A w a b c d l, zoneLevel a b c d (A.run w t).pos < l := by
  have hne := not_isRecognizedBy_palindromeBlocks_exists_level A w a b c d hd hl
  refine ⟨Nat.sInf_mem hne, fun t ht => ?_⟩
  have hnot := Nat.notMem_of_lt_sInf ht
  by_contra hge
  exact hnot (not_lt.mp hge)

/-- Step 2B0 of the proof of `not_isRecognizedBy_palindromeBlocks` (locality): the
transition function `A.next` depends on the input only through the symbols under the heads. -/
private lemma not_isRecognizedBy_palindromeBlocks_step2B0_next_congr {k : ℕ} {Sym Q : Type*}
    (A : MultiheadAutomaton k Sym Q) (v h : List Sym) (c : HeadConfig k Q)
    (hobs : ∀ x, v[c.pos x]? = h[c.pos x]?) : A.next v c = A.next h c := by
  have hobs' : MultiheadAutomaton.observe v c.pos = MultiheadAutomaton.observe h c.pos :=
    funext hobs
  have hT : MultiheadAutomaton.Terminated v c ↔ MultiheadAutomaton.Terminated h c := by
    unfold MultiheadAutomaton.Terminated
    rw [hobs']
  unfold MultiheadAutomaton.next
  by_cases h1 : MultiheadAutomaton.Terminated v c
  · rw [ite_eq_left h1, ite_eq_left (hT.mp h1)]
  · rw [ite_eq_right h1, ite_eq_right (fun h2 => h1 (hT.mpr h2))]
    simp only [hobs']

/-- Step 2B0 of the proof of `not_isRecognizedBy_palindromeBlocks`: the level time of
level `0` is `0`. -/
private lemma not_isRecognizedBy_palindromeBlocks_step2B0_levelTime_zero {k : ℕ} {Sym Q : Type*}
    (A : MultiheadAutomaton k Sym Q) (w : List Sym) (a b c d : ℕ) :
    levelTime A w a b c d 0 = 0 := by
  unfold levelTime
  exact Nat.eq_zero_of_le_zero (Nat.sInf_le (Nat.zero_le _))

/-- Step 2B0 of the proof of `not_isRecognizedBy_palindromeBlocks`: between the level
times `l` and `l + 1` of a run the zone of every head is constant (the zone of a head never
decreases, and the level, the sum of the zones, is `l` during this time). -/
private lemma not_isRecognizedBy_palindromeBlocks_step2B0_levelTime_stretch {k : ℕ}
    {Sym Q : Type*} (A : MultiheadAutomaton k Sym Q) (w : List Sym) (a b c d : ℕ)
    (hd : zone a b c d w.length = 4) {l : ℕ} (hl : l + 1 ≤ 4 * k) {t : ℕ}
    (ht1 : levelTime A w a b c d l ≤ t) (ht2 : t < levelTime A w a b c d (l + 1)) (x : Fin k) :
    zone a b c d ((A.run w t).pos x) =
      zone a b c d ((A.run w (levelTime A w a b c d l)).pos x) := by
  have hT := not_isRecognizedBy_palindromeBlocks_levelTime_spec A w a b c d hd (l := l) (by omega)
  have hT' := not_isRecognizedBy_palindromeBlocks_levelTime_spec A w a b c d hd (l := l + 1) hl
  have h1 : zoneLevel a b c d (A.run w t).pos < l + 1 := hT'.2 t ht2
  have h2 : zoneLevel a b c d (A.run w (levelTime A w a b c d l)).pos ≤
      zoneLevel a b c d (A.run w t).pos :=
    not_isRecognizedBy_palindromeBlocks_zoneLevel_run_mono A w a b c d ht1
  have heq : zoneLevel a b c d (A.run w (levelTime A w a b c d l)).pos =
      zoneLevel a b c d (A.run w t).pos := by
    have := hT.1
    omega
  unfold zoneLevel at heq
  have hle : ∀ y ∈ Finset.univ, zone a b c d ((A.run w (levelTime A w a b c d l)).pos y) ≤
      zone a b c d ((A.run w t).pos y) := fun y _ =>
    not_isRecognizedBy_palindromeBlocks_zone_mono
      (not_isRecognizedBy_palindromeBlocks_run_pos_mono A w y ht1)
  exact ((Finset.sum_eq_sum_iff_of_le hle).mp heq x (Finset.mem_univ x)).symm

/-- Step 2B0 of the proof of `not_isRecognizedBy_palindromeBlocks`: from the level time
of level `4 k` on, all heads are in zone `4`. -/
private lemma not_isRecognizedBy_palindromeBlocks_step2B0_zone_four {k : ℕ} {Sym Q : Type*}
    (A : MultiheadAutomaton k Sym Q) (w : List Sym) (a b c d : ℕ)
    (hd : zone a b c d w.length = 4) {t : ℕ} (ht : levelTime A w a b c d (4 * k) ≤ t)
    (x : Fin k) : zone a b c d ((A.run w t).pos x) = 4 := by
  have hT := not_isRecognizedBy_palindromeBlocks_levelTime_spec A w a b c d hd (l := 4 * k) le_rfl
  have hall : ∀ y, zone a b c d ((A.run w (levelTime A w a b c d (4 * k))).pos y) = 4 := by
    intro y
    by_contra hne
    have hlt : zone a b c d ((A.run w (levelTime A w a b c d (4 * k))).pos y) < 4 :=
      lt_of_le_of_ne (not_isRecognizedBy_palindromeBlocks_zone_le_four a b c d _) hne
    have hsum : ∑ x, zone a b c d ((A.run w (levelTime A w a b c d (4 * k))).pos x) <
        ∑ _x : Fin k, 4 :=
      Finset.sum_lt_sum (fun x _ => not_isRecognizedBy_palindromeBlocks_zone_le_four a b c d _)
        ⟨y, Finset.mem_univ y, hlt⟩
    have h4k : ∑ _x : Fin k, 4 = 4 * k := by simp [mul_comm]
    have := hT.1
    unfold zoneLevel at this
    omega
  have hmono := not_isRecognizedBy_palindromeBlocks_zone_mono (a := a) (b := b) (c := c) (d := d)
    (not_isRecognizedBy_palindromeBlocks_run_pos_mono A w x ht)
  have hle := not_isRecognizedBy_palindromeBlocks_zone_le_four a b c d ((A.run w t).pos x)
  have := hall x
  omega

/-- Auxiliary lemma for step 2B1: the symbol at position `p` of a word of the shape
`pre ++ X ++ mid ++ Z ++ post`, by cases on the part that contains `p`. -/
private lemma not_isRecognizedBy_palindromeBlocks_step2B1_getElem?_five {Sym : Type*}
    (pre X mid Z post : List Sym) (p : ℕ) :
    (pre ++ X ++ mid ++ Z ++ post)[p]? =
      if p < pre.length then pre[p]?
      else if p < pre.length + X.length then X[p - pre.length]?
      else if p < pre.length + X.length + mid.length then mid[p - (pre.length + X.length)]?
      else if p < pre.length + X.length + mid.length + Z.length then
        Z[p - (pre.length + X.length + mid.length)]?
      else post[p - (pre.length + X.length + mid.length + Z.length)]? := by
  simp only [List.getElem?_append, List.length_append]
  split_ifs <;> first | rfl | omega

/-- Step 2B1 of the proof of `not_isRecognizedBy_palindromeBlocks` (position bookkeeping
for the cut and paste): the words `u = pre ++ X ++ mid ++ X ++ post`, `u' = pre ++ Y ++ mid ++ Y ++
post` and `h = pre ++ X ++ mid ++ Y ++ post` (with `|X| = |Y|`) agree at every position outside the
two zones `[a, b)` (where `h` agrees with `u`) and `[c, d)` (where `h` agrees with `u'`), where
`a = |pre|`, `b = a + |X|`, `c = b + |mid|`, `d = c + |X|`.  Also `d ≤ |u|` and `|u'| = |u|`. -/
private lemma not_isRecognizedBy_palindromeBlocks_step2B1_zones {Sym : Type*}
    (pre mid post X Y : List Sym) (hXY : X.length = Y.length) (a b c d : ℕ)
    (ha : a = pre.length) (hb : b = a + X.length) (hc : c = b + mid.length)
    (hd : d = c + X.length) :
    (∀ p, (p < a ∨ (b ≤ p ∧ p < c) ∨ d ≤ p) →
      (pre ++ X ++ mid ++ X ++ post)[p]? = (pre ++ Y ++ mid ++ Y ++ post)[p]? ∧
      (pre ++ X ++ mid ++ X ++ post)[p]? = (pre ++ X ++ mid ++ Y ++ post)[p]?) ∧
    (∀ p, a ≤ p → p < b →
      (pre ++ X ++ mid ++ Y ++ post)[p]? = (pre ++ X ++ mid ++ X ++ post)[p]?) ∧
    (∀ p, c ≤ p → p < d →
      (pre ++ X ++ mid ++ Y ++ post)[p]? = (pre ++ Y ++ mid ++ Y ++ post)[p]?) ∧
    d ≤ (pre ++ X ++ mid ++ X ++ post).length ∧
    (pre ++ Y ++ mid ++ Y ++ post).length = (pre ++ X ++ mid ++ X ++ post).length := by
  subst ha
  subst hb
  subst hc
  subst hd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [not_isRecognizedBy_palindromeBlocks_step2B1_getElem?_five pre X mid X post p,
      not_isRecognizedBy_palindromeBlocks_step2B1_getElem?_five pre Y mid Y post p,
      not_isRecognizedBy_palindromeBlocks_step2B1_getElem?_five pre X mid Y post p]
    simp only [← hXY]
    split_ifs <;> first | exact ⟨rfl, rfl⟩ | omega
  · intro p hp1 hp2
    rw [not_isRecognizedBy_palindromeBlocks_step2B1_getElem?_five pre X mid X post p,
      not_isRecognizedBy_palindromeBlocks_step2B1_getElem?_five pre X mid Y post p]
    simp only [← hXY]
    split_ifs <;> rfl
  · intro p hp1 hp2
    rw [not_isRecognizedBy_palindromeBlocks_step2B1_getElem?_five pre Y mid Y post p,
      not_isRecognizedBy_palindromeBlocks_step2B1_getElem?_five pre X mid Y post p]
    simp only [← hXY]
    split_ifs <;> first | rfl | omega
  · simp only [List.length_append]
    omega
  · simp only [List.length_append]
    omega

/-- One step of the run. -/
private lemma not_isRecognizedBy_palindromeBlocks_run_succ {k : ℕ} {Sym Q : Type*}
    (A : MultiheadAutomaton k Sym Q) (w : List Sym) (t : ℕ) :
    A.run w (t + 1) = A.next w (A.run w t) :=
  Function.iterate_succ_apply' _ _ _

/-- If the run on `h` is at time `s` in the configuration of the run on `v` at time `T`, and during
the next `n` steps of the run on `v` the heads observe the same symbols on `v` and on `h`, then the
run on `h` follows the run on `v` for these `n` steps. -/
private lemma not_isRecognizedBy_palindromeBlocks_follow {k : ℕ} {Sym Q : Type*}
    (A : MultiheadAutomaton k Sym Q) (v h : List Sym) (s T n : ℕ)
    (hs : A.run h s = A.run v T)
    (hobs : ∀ j < n, ∀ x, v[(A.run v (T + j)).pos x]? = h[(A.run v (T + j)).pos x]?) :
    A.run h (s + n) = A.run v (T + n) := by
  induction n with
  | zero => simpa using hs
  | succ n ih =>
    have ih' := ih (fun j hj => hobs j (Nat.lt_succ_of_lt hj))
    change A.run h (s + n + 1) = A.run v (T + n + 1)
    rw [not_isRecognizedBy_palindromeBlocks_run_succ, not_isRecognizedBy_palindromeBlocks_run_succ,
      ih']
    exact (not_isRecognizedBy_palindromeBlocks_step2B0_next_congr A v h _
      (hobs n (Nat.lt_succ_self n))).symm

/-- Step 2B2 of the proof of `not_isRecognizedBy_palindromeBlocks` (copying one stretch
of the computation): suppose that the run of `A` on `h` is, at time `s`, in the configuration
`E_l = A.run v (levelTime A v a b c d l)` (state and all head positions), and that `h` and `v`
coincide on all positions whose zone is occupied by some head in `E_l`.  Between the times
`levelTime .. l` and `levelTime .. (l + 1)` of the run on `v` the zone of every head is constant
(the level is `l` there and the zone of a head never decreases), so the heads observe the same
symbols on `v` and on `h`, and by locality of the transition function the run on `h` follows the run
on `v`: after the same number of further steps it is in `E_{l+1}`.  (The end marker is in zone `4`,
which gives that the level times exist for `l + 1 ≤ 4 k`.) -/
private lemma not_isRecognizedBy_palindromeBlocks_step2B2_copyStretch {k : ℕ} {Sym Q : Type*}
    (A : MultiheadAutomaton k Sym Q) (v h : List Sym) (a b c d : ℕ)
    (hd : zone a b c d v.length = 4) (l : ℕ) (hl : l + 1 ≤ 4 * k) (s : ℕ)
    (hs : A.run h s = A.run v (levelTime A v a b c d l))
    (hag : ∀ (x : Fin k) (p : ℕ),
      zone a b c d p = zone a b c d ((A.run v (levelTime A v a b c d l)).pos x) →
        v[p]? = h[p]?) :
    ∃ s', A.run h s' = A.run v (levelTime A v a b c d (l + 1)) := by
  -- the level times are monotone: at the level time of `l + 1` the level is at least `l`
  have hle : levelTime A v a b c d l ≤ levelTime A v a b c d (l + 1) := by
    have hspec := not_isRecognizedBy_palindromeBlocks_levelTime_spec A v a b c d hd hl
    have hmem : levelTime A v a b c d (l + 1) ∈
        {t | l ≤ zoneLevel a b c d (A.run v t).pos} :=
      le_trans (Nat.le_succ l) hspec.1
    exact Nat.sInf_le hmem
  refine ⟨s + (levelTime A v a b c d (l + 1) - levelTime A v a b c d l), ?_⟩
  have key := not_isRecognizedBy_palindromeBlocks_follow A v h s (levelTime A v a b c d l)
    (levelTime A v a b c d (l + 1) - levelTime A v a b c d l) hs (fun j hj x => by
      apply hag x
      exact not_isRecognizedBy_palindromeBlocks_step2B0_levelTime_stretch A v a b c d hd hl
        (t := levelTime A v a b c d l + j) (by omega) (by omega) x)
  have e : levelTime A v a b c d l + (levelTime A v a b c d (l + 1) - levelTime A v a b c d l) =
      levelTime A v a b c d (l + 1) := by omega
  rw [e] at key
  exact key

/-- Step 2B3 of the proof of `not_isRecognizedBy_palindromeBlocks` (the end of the
cut-and-paste computation): if the run on `h` is at some time in the configuration `E_{4k}` of the
run on `v`, where all heads are in zone `4` (they have passed both copies of the block), and `h`
and `v` coincide on the positions of zone `4` (including the end marker), then `h` is accepted
whenever `v` is: from `E_{4k}` on, the run on `h` is the run on `v`. -/
private lemma not_isRecognizedBy_palindromeBlocks_step2B3_tail {k : ℕ} {Sym Q : Type*}
    (A : MultiheadAutomaton k Sym Q) (v h : List Sym) (a b c d : ℕ)
    (hd : zone a b c d v.length = 4) (s : ℕ)
    (hs : A.run h s = A.run v (levelTime A v a b c d (4 * k)))
    (hag : ∀ p, zone a b c d p = 4 → v[p]? = h[p]?) (hacc : A.Accepts v) :
    A.Accepts h := by
  obtain ⟨t0, hterm, hacc0⟩ := hacc
  -- once terminated, the configuration stays the same
  have hpers : ∀ j, A.run v (t0 + j) = A.run v t0 := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      change A.run v (t0 + j + 1) = A.run v t0
      rw [not_isRecognizedBy_palindromeBlocks_run_succ, ih]
      unfold MultiheadAutomaton.next
      rw [ite_eq_left hterm]
  generalize hT : levelTime A v a b c d (4 * k) = T at hs
  have hfollow : ∀ j, A.run h (s + j) = A.run v (T + j) := fun j =>
    not_isRecognizedBy_palindromeBlocks_follow A v h s T j hs (fun i _ x => by
      apply hag
      exact not_isRecognizedBy_palindromeBlocks_step2B0_zone_four A v a b c d hd
        (t := T + i) (by rw [hT]; omega) x)
  refine ⟨s + (max t0 T - T), ?_⟩
  have e1 : T + (max t0 T - T) = t0 + (max t0 T - t0) := by omega
  have hrun : A.run h (s + (max t0 T - T)) = A.run v t0 := by
    rw [hfollow, e1, hpers]
  rw [hrun]
  refine ⟨fun x => ?_, hacc0⟩
  have hz : zone a b c d ((A.run v t0).pos x) = 4 := by
    have := not_isRecognizedBy_palindromeBlocks_step2B0_zone_four A v a b c d hd
      (t := t0 + (max t0 T - t0)) (by rw [hT]; omega) x
    rwa [hpers] at this
  have hvh := hag _ hz
  have hv := hterm x
  simp only [MultiheadAutomaton.observe] at hv ⊢
  rw [← hvh]
  exact hv

/-- Step 2B of the proof of `not_isRecognizedBy_palindromeBlocks` (cutting and pasting
computations, p. 250 of the chapter text): `u`, `u'`, `h` are three words which agree outside the
zones `[a, b)` (where `h` agrees with `u`) and `[c, d)` (where `h` agrees with `u'`), the run on
`u` never has one head in `[a, b)` and another one in `[c, d)`, and the protocols of the runs on
`u` and `u'` coincide (same state and same head positions at the times `levelTime .. l`,
`l ≤ 4 k`).  Then `A` accepts `h` if it accepts `u`.  Proof: by induction on `l`, the run on `h`
reaches the configuration `E_l`; between `E_l` and `E_{l+1}` either no head is in zone `3` (copy the
stretch from `u`) or no head is in zone `1` (copy it from `u'`, whose configuration `E_l` is the
same); finally copy the tail from `u`. -/
private lemma not_isRecognizedBy_palindromeBlocks_step2B_cutAndPaste {k : ℕ} {Sym Q : Type*}
    (A : MultiheadAutomaton k Sym Q) (u u' h : List Sym) (a b c d : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hdu : d ≤ u.length)
    (hlen : u'.length = u.length)
    (h0 : ∀ p, (p < a ∨ (b ≤ p ∧ p < c) ∨ d ≤ p) → u[p]? = u'[p]? ∧ u[p]? = h[p]?)
    (h1 : ∀ p, a ≤ p → p < b → h[p]? = u[p]?)
    (h3 : ∀ p, c ≤ p → p < d → h[p]? = u'[p]?)
    (hno : ¬ ∃ (t : ℕ) (x y : Fin k), a ≤ (A.run u t).pos x ∧ (A.run u t).pos x < b ∧
      c ≤ (A.run u t).pos y ∧ (A.run u t).pos y < d)
    (hE : ∀ l ≤ 4 * k,
      A.run u (levelTime A u a b c d l) = A.run u' (levelTime A u' a b c d l)) :
    A.Accepts u → A.Accepts h := by
  intro hacc
  have hdu4 : zone a b c d u.length = 4 := by
    unfold zone; split_ifs <;> omega
  have hdu'4 : zone a b c d u'.length = 4 := by rw [hlen]; exact hdu4
  have key : ∀ l, l ≤ 4 * k → ∃ s, A.run h s = A.run u (levelTime A u a b c d l) := by
    intro l
    induction l with
    | zero =>
      intro _
      refine ⟨0, ?_⟩
      rw [not_isRecognizedBy_palindromeBlocks_step2B0_levelTime_zero]
      simp [MultiheadAutomaton.run]
    | succ l ih =>
      intro hl
      obtain ⟨s, hs⟩ := ih (by omega)
      by_cases hJ : ∃ x : Fin k, zone a b c d ((A.run u (levelTime A u a b c d l)).pos x) = 3
      · by_cases hI : ∃ x : Fin k, zone a b c d ((A.run u (levelTime A u a b c d l)).pos x) = 1
        · exfalso
          obtain ⟨y, hy⟩ := hJ
          obtain ⟨x, hx⟩ := hI
          apply hno
          refine ⟨levelTime A u a b c d l, x, y, ?_⟩
          rcases not_isRecognizedBy_palindromeBlocks_zone_cases (a := a) (b := b) (c := c) (d := d)
            (p := (A.run u (levelTime A u a b c d l)).pos x) hbc hcd with
            hz | hz | hz | hz | hz <;>
          rcases not_isRecognizedBy_palindromeBlocks_zone_cases (a := a) (b := b) (c := c) (d := d)
            (p := (A.run u (levelTime A u a b c d l)).pos y) hbc hcd with
            hz' | hz' | hz' | hz' | hz' <;> omega
        · -- no head in zone 1: copy the stretch from `u'`
          push Not at hI
          have hE' := hE l (by omega)
          obtain ⟨s', hs'⟩ := not_isRecognizedBy_palindromeBlocks_step2B2_copyStretch A u' h a b c d
            hdu'4 l hl s (hs.trans hE') (by
              intro x p hp
              rw [← hE'] at hp
              have hx := hI x
              rcases not_isRecognizedBy_palindromeBlocks_zone_cases (a := a) (b := b) (c := c)
                (d := d) (p := p) hbc hcd with hz | hz | hz | hz | hz
              · exact ((h0 p (Or.inl hz.2)).1.symm.trans (h0 p (Or.inl hz.2)).2)
              · omega
              · exact ((h0 p (Or.inr (Or.inl hz.2))).1.symm.trans
                  (h0 p (Or.inr (Or.inl hz.2))).2)
              · exact (h3 p hz.2.1 hz.2.2).symm
              · exact ((h0 p (Or.inr (Or.inr hz.2))).1.symm.trans
                  (h0 p (Or.inr (Or.inr hz.2))).2))
          exact ⟨s', hs'.trans (hE (l + 1) hl).symm⟩
      · -- no head in zone 3: copy the stretch from `u`
        push Not at hJ
        exact not_isRecognizedBy_palindromeBlocks_step2B2_copyStretch A u h a b c d hdu4 l hl s hs
            (by
          intro x p hp
          have hx := hJ x
          rcases not_isRecognizedBy_palindromeBlocks_zone_cases (a := a) (b := b) (c := c)
            (d := d) (p := p) hbc hcd with hz | hz | hz | hz | hz
          · exact (h0 p (Or.inl hz.2)).2
          · exact (h1 p hz.2.1 hz.2.2).symm
          · exact (h0 p (Or.inr (Or.inl hz.2))).2
          · omega
          · exact (h0 p (Or.inr (Or.inr hz.2))).2)
  obtain ⟨s, hs⟩ := key (4 * k) le_rfl
  refine not_isRecognizedBy_palindromeBlocks_step2B3_tail A u h a b c d hdu4 s hs ?_ hacc
  intro p hp
  rcases not_isRecognizedBy_palindromeBlocks_zone_cases (a := a) (b := b) (c := c)
    (d := d) (p := p) hbc hcd with hz | hz | hz | hz | hz <;> try omega
  exact (h0 p (Or.inr (Or.inr hz.2))).2

/-- Auxiliary for step 2C: `j² ≤ 2^j` for `j ≥ 4`. -/
private lemma not_isRecognizedBy_palindromeBlocks_sq_le_two_pow (j : ℕ) (hj : 4 ≤ j) :
    j * j ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => decide
  | succ j hj ih =>
    have h1 : 4 * j ≤ j * j := Nat.mul_le_mul_right j hj
    have h2 : (j + 1) * (j + 1) = j * j + 2 * j + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    rw [Nat.pow_succ, h2]
    omega

/-- Auxiliary for step 2C: exponentials beat polynomials, `C * n ^ d < 2 ^ n` for some `n ≥ 1`. -/
private lemma not_isRecognizedBy_palindromeBlocks_poly_lt_two_pow (C d : ℕ) :
    ∃ n : ℕ, 1 ≤ n ∧ C * n ^ d < 2 ^ n := by
  obtain ⟨j, hj⟩ : ∃ j, j = C + d + 4 := ⟨_, rfl⟩
  have hj4 : 4 ≤ j := by omega
  have hsq := not_isRecognizedBy_palindromeBlocks_sq_le_two_pow j hj4
  have hlin : C + j * d ≤ 2 ^ j := by
    have h1 : C ≤ j * C := Nat.le_mul_of_pos_left C (by omega)
    have h2 : j * (C + d) ≤ j * j := Nat.mul_le_mul_left j (by omega)
    have h3 : j * (C + d) = j * C + j * d := Nat.mul_add j C d
    omega
  refine ⟨2 ^ j, Nat.one_le_two_pow, ?_⟩
  calc C * (2 ^ j) ^ d = C * 2 ^ (j * d) := by rw [← Nat.pow_mul]
    _ < 2 ^ C * 2 ^ (j * d) :=
        Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (Nat.two_pow_pos _)
    _ = 2 ^ (C + j * d) := by rw [← Nat.pow_add]
    _ ≤ 2 ^ (2 ^ j) := Nat.pow_le_pow_right (by decide) hlin

/-- Auxiliary for step 2C: a finset of exactly `2 ^ n` lists, the bit strings of length `n`. -/
private lemma not_isRecognizedBy_palindromeBlocks_exists_bitStrings (n : ℕ) :
    ∃ Ln : Finset (List Bool), Ln.card = 2 ^ n ∧ ∀ l, l ∈ Ln ↔ l.length = n := by
  classical
  refine ⟨(Finset.univ : Finset (Fin n → Bool)).image List.ofFn, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ List.ofFn_injective]
    simp
  · intro l
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨f, rfl⟩
      simp
    · intro hl
      subst hl
      exact ⟨l.get, List.ofFn_get l⟩

/-- Auxiliary for step 2C: a finset of at most `|Q| (B + 1)^k` configurations containing all
configurations with all head positions at most `B`. -/
private lemma not_isRecognizedBy_palindromeBlocks_exists_configs {k : ℕ} {Q : Type*} [Fintype Q]
    (B : ℕ) : ∃ Cfg : Finset (HeadConfig k Q),
      Cfg.card ≤ Fintype.card Q * (B + 1) ^ k ∧
      ∀ c : HeadConfig k Q, (∀ x, c.pos x ≤ B) → c ∈ Cfg := by
  classical
  refine ⟨(Finset.univ ×ˢ Fintype.piFinset (fun _ : Fin k => Finset.range (B + 1))).image
      (fun p => (⟨p.1, p.2⟩ : HeadConfig k Q)), ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Fintype.card_piFinset]
    simp
  · intro c hc
    rw [Finset.mem_image]
    refine ⟨(c.state, c.pos), ?_, rfl⟩
    simp [Fintype.mem_piFinset, Nat.lt_succ_iff, hc]

/-- Auxiliary for step 2C: the number of tuples whose block `i` is empty and whose other blocks lie
in `Ln`. -/
private lemma not_isRecognizedBy_palindromeBlocks_card_erased {m : ℕ} (i : Fin m)
    (Ln : Finset (List Bool)) :
    (Fintype.piFinset (fun j : Fin m => if j = i then ({[]} : Finset (List Bool)) else Ln)).card
      = Ln.card ^ (m - 1) := by
  classical
  rw [Fintype.card_piFinset]
  have h : ∀ j : Fin m, (if j = i then ({[]} : Finset (List Bool)) else Ln).card =
      if j = i then 1 else Ln.card := by
    intro j
    split_ifs <;> simp
  simp only [h]
  rw [Finset.prod_ite]
  simp [Finset.filter_ne', Finset.card_erase_of_mem]

/-- Step 2C of the proof of `not_isRecognizedBy_palindromeBlocks` (counting instead of
Kolmogorov complexity): for every `n` let `i0 n w` be a block index and `E n w l` a configuration
(state and head positions) of a machine with finitely many states, with all positions at most
`2 m n + 2 m` whenever all blocks of `w` have length `n`.  Then for `n` large enough, there are two
different tuples `w ≠ w'` of blocks of length `n` which differ only in the block `i0 n w = i0 n w'`
and have the same configurations `E n w l = E n w' l` for all `l ≤ 4 k`: the map
`w ↦ (i0 w, w without its block i0 w, (E n w l)_{l ≤ 4k})` takes at most
`m · 2^{n (m - 1)} · (|Q| (2 m n + 2 m + 1)^k)^{4 k + 1}` values on the `2^{n m}` tuples, and
`m · (|Q| (2 m n + 2 m + 1)^k)^{4 k + 1} < 2^n` for large `n`; apply the pigeonhole principle. -/
private lemma not_isRecognizedBy_palindromeBlocks_step2C_pigeonhole {k m : ℕ} {Q : Type*}
    [Finite Q] (i0 : ℕ → (Fin m → List Bool) → Fin m)
    (E : ℕ → (Fin m → List Bool) → ℕ → HeadConfig k Q)
    (hE : ∀ n w l, (∀ j, (w j).length = n) → ∀ x, (E n w l).pos x ≤ 2 * m * n + 2 * m) :
    ∃ (n : ℕ) (w w' : Fin m → List Bool),
      (∀ j, (w j).length = n) ∧ (∀ j, (w' j).length = n) ∧ w ≠ w' ∧
      i0 n w = i0 n w' ∧ (∀ j, j ≠ i0 n w → w j = w' j) ∧
      ∀ l ≤ 4 * k, E n w l = E n w' l := by
  classical
  cases nonempty_fintype Q
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact (i0 0 (fun j => j.elim0)).elim0
  -- choose `n` so large that the number of protocols is below `2 ^ n / m`
  obtain ⟨n, hn1, hn⟩ := not_isRecognizedBy_palindromeBlocks_poly_lt_two_pow
    (m * Fintype.card Q ^ (4 * k + 1) * (5 * m) ^ (k * (4 * k + 1))) (k * (4 * k + 1))
  obtain ⟨Ln, hLn_card, hLn_mem⟩ := not_isRecognizedBy_palindromeBlocks_exists_bitStrings n
  obtain ⟨Cfg, hCfg_card, hCfg_mem⟩ :=
    not_isRecognizedBy_palindromeBlocks_exists_configs (k := k) (Q := Q) (2 * m * n + 2 * m)
  obtain ⟨R, hR⟩ : ∃ R : ℕ,
      R = (Fintype.card Q * (2 * m * n + 2 * m + 1) ^ k) ^ (4 * k + 1) := ⟨_, rfl⟩
  have hkey : m * R < 2 ^ n := by
    have h1 : 2 * m * n + 2 * m + 1 ≤ 5 * m * n := by
      have h2 : m ≤ m * n := Nat.le_mul_of_pos_right m hn1
      have e1 : 2 * m * n = 2 * (m * n) := Nat.mul_assoc 2 m n
      have e2 : 5 * m * n = 5 * (m * n) := Nat.mul_assoc 5 m n
      omega
    calc m * R = m * (Fintype.card Q ^ (4 * k + 1) *
            (2 * m * n + 2 * m + 1) ^ (k * (4 * k + 1))) := by
          rw [hR, Nat.mul_pow, ← Nat.pow_mul]
      _ ≤ m * (Fintype.card Q ^ (4 * k + 1) * (5 * m * n) ^ (k * (4 * k + 1))) :=
          Nat.mul_le_mul_left m (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _))
      _ = (m * Fintype.card Q ^ (4 * k + 1) * (5 * m) ^ (k * (4 * k + 1))) *
            n ^ (k * (4 * k + 1)) := by
          rw [Nat.mul_pow]
          simp only [Nat.mul_assoc]
      _ < 2 ^ n := hn
  -- the family of all tuples of blocks of length `n`
  obtain ⟨s, hs⟩ : ∃ s : Finset (Fin m → List Bool), s = Fintype.piFinset (fun _ => Ln) :=
    ⟨_, rfl⟩
  have hs_mem : ∀ w, w ∈ s ↔ ∀ j, (w j).length = n := by
    intro w
    simp [hs, Fintype.mem_piFinset, hLn_mem]
  have hs_card : s.card = (2 ^ n) ^ m := by
    rw [hs, Fintype.card_piFinset]
    simp [hLn_card]
  -- first pigeonhole: some block index `i` is `i0 n w` for many tuples `w`
  have hlt1 : m * ((2 ^ n) ^ (m - 1) * R) < s.card := by
    rw [hs_card]
    have hpow : (2 ^ n) ^ m = (2 ^ n) ^ (m - 1) * 2 ^ n := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow]
    calc m * ((2 ^ n) ^ (m - 1) * R) = (2 ^ n) ^ (m - 1) * (m * R) := Nat.mul_left_comm m _ R
      _ < (2 ^ n) ^ (m - 1) * 2 ^ n :=
          (Nat.mul_lt_mul_left (Nat.pow_pos (Nat.two_pow_pos n))).2 hkey
  obtain ⟨i, hi⟩ : ∃ i : Fin m,
      (2 ^ n) ^ (m - 1) * R < (s.filter (fun w => i0 n w = i)).card := by
    by_contra hcon
    have hcon' : ∀ i : Fin m, (s.filter (fun w => i0 n w = i)).card ≤ (2 ^ n) ^ (m - 1) * R :=
      fun i => not_lt.1 (fun h => hcon ⟨i, h⟩)
    have hsum : s.card = ∑ i : Fin m, (s.filter (fun w => i0 n w = i)).card :=
      Finset.card_eq_sum_card_fiberwise (fun w _ => Finset.mem_univ _)
    have hle : s.card ≤ m * ((2 ^ n) ^ (m - 1) * R) := by
      rw [hsum]
      calc ∑ i : Fin m, (s.filter (fun w => i0 n w = i)).card
          ≤ ∑ _i : Fin m, (2 ^ n) ^ (m - 1) * R := Finset.sum_le_sum (fun i _ => hcon' i)
        _ = m * ((2 ^ n) ^ (m - 1) * R) := by simp
    omega
  -- second pigeonhole: two tuples with the same block `i0 n w = i` agree outside `i` and
  -- have the same protocol
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin m → List Bool), T = Fintype.piFinset
      (fun j : Fin m => if j = i then ({[]} : Finset (List Bool)) else Ln) := ⟨_, rfl⟩
  obtain ⟨Pset, hPset⟩ : ∃ Pset : Finset (Fin (4 * k + 1) → HeadConfig k Q),
      Pset = Fintype.piFinset (fun _ => Cfg) := ⟨_, rfl⟩
  have hT_card : T.card = (2 ^ n) ^ (m - 1) := by
    rw [hT, not_isRecognizedBy_palindromeBlocks_card_erased, hLn_card]
  have hP_card : Pset.card ≤ R := by
    rw [hPset, Fintype.card_piFinset, hR]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact Nat.pow_le_pow_left hCfg_card _
  have hlt2 : (T ×ˢ Pset).card < (s.filter (fun w => i0 n w = i)).card := by
    rw [Finset.card_product, hT_card]
    calc (2 ^ n) ^ (m - 1) * Pset.card ≤ (2 ^ n) ^ (m - 1) * R := Nat.mul_le_mul_left _ hP_card
      _ < _ := hi
  obtain ⟨w, hw, w', hw', hne, hg⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt2
    (f := fun w => (Function.update w i [], fun l : Fin (4 * k + 1) => E n w l)) (by
      intro w hw
      rw [Finset.mem_coe, Finset.mem_filter] at hw
      have hws := (hs_mem w).1 hw.1
      rw [Finset.mem_coe]
      change (Function.update w i [], fun l : Fin (4 * k + 1) => E n w l) ∈ T ×ˢ Pset
      rw [Finset.mem_product, hT, hPset, Fintype.mem_piFinset, Fintype.mem_piFinset]
      refine ⟨fun j => ?_, fun l => hCfg_mem _ (hE n w l hws)⟩
      by_cases hj : j = i
      · subst hj
        simp
      · simp only [Function.update_of_ne hj, hj, ↓reduceIte]
        exact (hLn_mem _).2 (hws j))
  rw [Finset.mem_filter] at hw hw'
  have hwn := (hs_mem w).1 hw.1
  have hwn' := (hs_mem w').1 hw'.1
  refine ⟨n, w, w', hwn, hwn', hne, by rw [hw.2, hw'.2], ?_, ?_⟩
  · intro j hj
    rw [hw.2] at hj
    have := congr_fun (Prod.mk.inj hg).1 j
    simpa [Function.update_of_ne hj] using this
  · intro l hl
    have := congr_fun (Prod.mk.inj hg).2 ⟨l, by omega⟩
    simpa using this

/-- Unfolding `blockWord` at the first of at least two blocks. -/
private lemma not_isRecognizedBy_palindromeBlocks_blockWord_cons_ne {a : List Bool}
    {t : List (List Bool)} (ht : t ≠ []) :
    blockWord (a :: t) = a.map BlockSymbol.bit ++ BlockSymbol.sep :: blockWord t := by
  unfold blockWord
  rw [List.map_cons, List.intercalate_cons_of_ne_nil (by simpa using ht)]
  simp

/-- `blockWord` of a nonempty list: the first block, then each further block preceded by a
separator. -/
private lemma not_isRecognizedBy_palindromeBlocks_blockWord_cons (a : List Bool)
    (t : List (List Bool)) :
    blockWord (a :: t) = a.map BlockSymbol.bit ++
      (t.map (fun b => BlockSymbol.sep :: b.map BlockSymbol.bit)).flatten := by
  induction t generalizing a with
  | nil => simp [blockWord]
  | cons b t ih =>
    rw [not_isRecognizedBy_palindromeBlocks_blockWord_cons_ne (List.cons_ne_nil b t), ih b]
    simp

/-- `blockWord` of an append: the first blocks, each followed by a separator, then the rest. -/
private lemma not_isRecognizedBy_palindromeBlocks_blockWord_append {L1 R : List (List Bool)}
    (hR : R ≠ []) :
    blockWord (L1 ++ R) =
      (L1.map (fun b => b.map BlockSymbol.bit ++ [BlockSymbol.sep])).flatten ++ blockWord R := by
  induction L1 with
  | nil => simp
  | cons a L1 ih =>
    have hne : L1 ++ R ≠ [] := fun h => hR (List.append_eq_nil_iff.mp h).2
    rw [List.cons_append, not_isRecognizedBy_palindromeBlocks_blockWord_cons_ne hne, ih]
    simp

/-- The word of a list of blocks with two distinguished blocks `x`, `y`. -/
private lemma not_isRecognizedBy_palindromeBlocks_blockWord_split
    (L1 L2 L3 : List (List Bool)) (x y : List Bool) :
    blockWord (L1 ++ x :: (L2 ++ y :: L3)) =
      (L1.map (fun b => b.map BlockSymbol.bit ++ [BlockSymbol.sep])).flatten ++
        x.map BlockSymbol.bit ++
        ((L2.map (fun b => BlockSymbol.sep :: b.map BlockSymbol.bit)).flatten ++
          [BlockSymbol.sep]) ++
        y.map BlockSymbol.bit ++
        (L3.map (fun b => BlockSymbol.sep :: b.map BlockSymbol.bit)).flatten := by
  rw [not_isRecognizedBy_palindromeBlocks_blockWord_append (List.cons_ne_nil _ _),
    not_isRecognizedBy_palindromeBlocks_blockWord_cons]
  simp [List.map_append, List.flatten_append]

/-- Splitting `List.ofFn` at an index. -/
private lemma not_isRecognizedBy_palindromeBlocks_ofFn_split {m : ℕ} (w : Fin m → List Bool)
    (i : Fin m) :
    List.ofFn w = (List.ofFn w).take (i : ℕ) ++ w i :: (List.ofFn w).drop ((i : ℕ) + 1) := by
  have hi : (i : ℕ) < (List.ofFn w).length := by simp
  conv_lhs => rw [← List.take_append_drop (i : ℕ) (List.ofFn w)]
  rw [List.drop_eq_getElem_cons hi]
  simp

/-- The word `mixedWord v v'` cut at the index `i`. -/
private lemma not_isRecognizedBy_palindromeBlocks_mixedWord_eq {m : ℕ} (v v' : Fin m → List Bool)
    (i : Fin m) :
    mixedWord v v' =
      (((List.ofFn v).take (i : ℕ)).map
          (fun b => b.map BlockSymbol.bit ++ [BlockSymbol.sep])).flatten ++
        (v i).map BlockSymbol.bit ++
        (((((List.ofFn v).drop ((i : ℕ) + 1)) ++ ((List.ofFn v').drop ((i : ℕ) + 1)).reverse).map
            (fun b => BlockSymbol.sep :: b.map BlockSymbol.bit)).flatten ++
          [BlockSymbol.sep]) ++
        (v' i).map BlockSymbol.bit ++
        ((((List.ofFn v').take (i : ℕ)).reverse).map
          (fun b => BlockSymbol.sep :: b.map BlockSymbol.bit)).flatten := by
  have key : List.ofFn v ++ (List.ofFn v').reverse =
      (List.ofFn v).take (i : ℕ) ++ v i ::
        (((List.ofFn v).drop ((i : ℕ) + 1) ++ ((List.ofFn v').drop ((i : ℕ) + 1)).reverse) ++
          v' i :: ((List.ofFn v').take (i : ℕ)).reverse) := by
    conv_lhs =>
      rw [not_isRecognizedBy_palindromeBlocks_ofFn_split v i,
        not_isRecognizedBy_palindromeBlocks_ofFn_split v' i]
    simp
  unfold mixedWord
  rw [key, not_isRecognizedBy_palindromeBlocks_blockWord_split]

/-- Two tuples agreeing outside `i` have the same initial segments before `i`. -/
private lemma not_isRecognizedBy_palindromeBlocks_take_eq {m : ℕ} (w w' : Fin m → List Bool)
    (i : Fin m) (hag : ∀ j, j ≠ i → w j = w' j) :
    (List.ofFn w').take (i : ℕ) = (List.ofFn w).take (i : ℕ) := by
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    have hj : j < (i : ℕ) := by
      have := h₁
      simp [List.length_take] at this
      omega
    have hjm : j < m := by omega
    simp only [List.getElem_take, List.getElem_ofFn]
    exact (hag ⟨j, hjm⟩ (fun h => by
      have := congrArg Fin.val h
      simp at this
      omega)).symm

/-- Two tuples agreeing outside `i` have the same final segments after `i`. -/
private lemma not_isRecognizedBy_palindromeBlocks_drop_eq {m : ℕ} (w w' : Fin m → List Bool)
    (i : Fin m) (hag : ∀ j, j ≠ i → w j = w' j) :
    (List.ofFn w').drop ((i : ℕ) + 1) = (List.ofFn w).drop ((i : ℕ) + 1) := by
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    have hj : (i : ℕ) + 1 + j < m := by
      have := h₁
      simp [List.length_drop] at this
      omega
    simp only [List.getElem_drop, List.getElem_ofFn]
    exact (hag ⟨(i : ℕ) + 1 + j, hj⟩ (fun h => by
      have := congrArg Fin.val h
      simp at this
      omega)).symm

/-- A list of blocks of length `n`, each followed by a separator, has `(n + 1)` symbols per block.
-/
private lemma not_isRecognizedBy_palindromeBlocks_length_T (n : ℕ) (L : List (List Bool))
    (hL : ∀ b ∈ L, b.length = n) :
    ((L.map (fun b => b.map BlockSymbol.bit ++ [BlockSymbol.sep])).flatten).length =
      L.length * (n + 1) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha : a.length = n := hL a (List.mem_cons_self ..)
    have ih' := ih (fun b hb => hL b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_map,
      List.length_cons, List.length_nil, ha, ih']
    rw [Nat.succ_mul]
    omega

/-- A list of blocks of length `n`, each preceded by a separator, has `(n + 1)` symbols per block.
-/
private lemma not_isRecognizedBy_palindromeBlocks_length_S (n : ℕ) (L : List (List Bool))
    (hL : ∀ b ∈ L, b.length = n) :
    ((L.map (fun b => BlockSymbol.sep :: b.map BlockSymbol.bit)).flatten).length =
      L.length * (n + 1) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha : a.length = n := hL a (List.mem_cons_self ..)
    have ih' := ih (fun b hb => hL b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_map,
      List.length_cons, ha, ih']
    rw [Nat.succ_mul]
    omega

/-- Step 2D2 of the proof of `not_isRecognizedBy_palindromeBlocks` (layout of the words):
if the tuples `w`, `w'` of blocks of length `n` agree outside the block `i`, then
`mixedWord w w`, `mixedWord w' w'` and `mixedWord w w'` all have the form
`pre ++ X ++ mid ++ Y ++ post` with the same `pre`, `mid`, `post`, where `X, Y` is the left, right
copy of block `i` (`X = Y = w i` for `mixedWord w w`, etc.), `|pre| = i (n + 1)` (the `i` earlier
blocks, each followed by a separator) and `|mid| = 2 (m - 1 - i) (n + 1) + 1` (the blocks between
the two copies of block `i`, with their separators, and one more separator). -/
private lemma not_isRecognizedBy_palindromeBlocks_step2D2_decomp {m : ℕ} (n : ℕ) (i : Fin m)
    (w w' : Fin m → List Bool) (hw : ∀ j, (w j).length = n) (hag : ∀ j, j ≠ i → w j = w' j) :
    ∃ pre mid post : List BlockSymbol,
      pre.length = i * (n + 1) ∧ mid.length = 2 * (m - 1 - i) * (n + 1) + 1 ∧
      mixedWord w w = pre ++ (w i).map BlockSymbol.bit ++ mid ++ (w i).map BlockSymbol.bit ++ post ∧
      mixedWord w' w' =
        pre ++ (w' i).map BlockSymbol.bit ++ mid ++ (w' i).map BlockSymbol.bit ++ post ∧
      mixedWord w w' = pre ++ (w i).map BlockSymbol.bit ++ mid ++ (w' i).map BlockSymbol.bit ++
          post := by
  have ht := not_isRecognizedBy_palindromeBlocks_take_eq w w' i hag
  have hd := not_isRecognizedBy_palindromeBlocks_drop_eq w w' i hag
  have e1 := not_isRecognizedBy_palindromeBlocks_mixedWord_eq w w i
  have e2 := not_isRecognizedBy_palindromeBlocks_mixedWord_eq w' w' i
  have e3 := not_isRecognizedBy_palindromeBlocks_mixedWord_eq w w' i
  rw [ht, hd] at e2 e3
  have hL1 : ∀ b ∈ (List.ofFn w).take (i : ℕ), b.length = n := by
    intro b hb
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hb)
    exact hw j
  have hLm : ∀ b ∈ (List.ofFn w).drop ((i : ℕ) + 1), b.length = n := by
    intro b hb
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop hb)
    exact hw j
  have hLmm : ∀ b ∈ ((List.ofFn w).drop ((i : ℕ) + 1) ++
      ((List.ofFn w).drop ((i : ℕ) + 1)).reverse), b.length = n := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hLm b hb
    · exact hLm b (List.mem_reverse.mp hb)
  refine ⟨(((List.ofFn w).take (i : ℕ)).map
      (fun b => b.map BlockSymbol.bit ++ [BlockSymbol.sep])).flatten,
    (((((List.ofFn w).drop ((i : ℕ) + 1)) ++ ((List.ofFn w).drop ((i : ℕ) + 1)).reverse).map
        (fun b => BlockSymbol.sep :: b.map BlockSymbol.bit)).flatten ++ [BlockSymbol.sep]),
    ((((List.ofFn w).take (i : ℕ)).reverse).map
      (fun b => BlockSymbol.sep :: b.map BlockSymbol.bit)).flatten, ?_, ?_, e1, e2, e3⟩
  · rw [not_isRecognizedBy_palindromeBlocks_length_T n _ hL1]
    have : ((List.ofFn w).take (i : ℕ)).length = (i : ℕ) := by
      simp [List.length_take]
    rw [this]
  · rw [List.length_append, not_isRecognizedBy_palindromeBlocks_length_S n _ hLmm,
      List.length_singleton]
    have : ((List.ofFn w).drop ((i : ℕ) + 1) ++
        ((List.ofFn w).drop ((i : ℕ) + 1)).reverse).length = 2 * (m - 1 - (i : ℕ)) := by
      simp only [List.length_append, List.length_reverse, List.length_drop, List.length_ofFn]
      omega
    rw [this]

/-- Auxiliary lemma for step 2D4: the word `blockWord L` has at most one symbol more than the total
length of the blocks per block (`n` bits and at most one separator per block). -/
private lemma not_isRecognizedBy_palindromeBlocks_step2D4_blockWord_length_le
    (L : List (List Bool)) :
    (blockWord L).length ≤ (L.map fun b => b.length + 1).sum := by
  induction L with
  | nil => simp [blockWord]
  | cons a t ih =>
    cases t with
    | nil => simp [blockWord]
    | cons b t' =>
      have hne : (b :: t').map (fun c : List Bool => c.map BlockSymbol.bit) ≠ [] := by simp
      have hcons : blockWord (a :: b :: t') =
          a.map BlockSymbol.bit ++ [BlockSymbol.sep] ++ blockWord (b :: t') := by
        unfold blockWord
        rw [List.map_cons, List.intercalate_cons_of_ne_nil hne]
      rw [hcons]
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
        List.map_cons, List.sum_cons] at ih ⊢
      omega

/-- Step 2D4 of the proof of `not_isRecognizedBy_palindromeBlocks` (length bound): if all
blocks have length `n`, the word `mixedWord w w'` has at most `2 m (n + 1)` symbols (`2 m` blocks of
`n` bits, each with at most one separator). -/
private lemma not_isRecognizedBy_palindromeBlocks_step2D4_length {m n : ℕ}
    (w w' : Fin m → List Bool) (hw : ∀ j, (w j).length = n) (hw' : ∀ j, (w' j).length = n) :
    (mixedWord w w').length ≤ 2 * m * n + 2 * m := by
  have hsum : ∀ v : Fin m → List Bool, (∀ j, (v j).length = n) →
      ((List.ofFn v).map fun b => b.length + 1).sum = m * (n + 1) := by
    intro v hv
    rw [List.map_ofFn]
    have hfun : ((fun b : List Bool => b.length + 1) ∘ v) = fun _ => n + 1 := by
      funext j
      simp [hv j]
    rw [hfun, List.ofFn_const, List.sum_replicate_nat]
  refine le_trans (not_isRecognizedBy_palindromeBlocks_step2D4_blockWord_length_le _) ?_
  rw [List.map_append, List.sum_append, List.map_reverse, List.sum_reverse, hsum w hw,
    hsum w' hw', Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  omega

/-- Step 2D0 of the proof of `not_isRecognizedBy_palindromeBlocks`: a head never moves
to the left. -/
private lemma not_isRecognizedBy_palindromeBlocks_step2D0_pos_succ {k : ℕ} {Sym Q : Type*}
    (A : MultiheadAutomaton k Sym Q) (w : List Sym) (t : ℕ) (x : Fin k) :
    (A.run w t).pos x ≤ (A.run w (t + 1)).pos x := by
  have hrun : A.run w (t + 1) = A.next w (A.run w t) := Function.iterate_succ_apply' _ _ _
  rw [hrun]
  unfold MultiheadAutomaton.next
  split_ifs with hterm
  · exact le_rfl
  · dsimp only
    split_ifs with hmove
    · omega
    · exact le_rfl

/-- Step 2D of the proof of `not_isRecognizedBy_palindromeBlocks` (gluing steps 2A, 2B,
2C): a `k`-head automaton `A` with finitely many states, `m > k.choose 2`, can be "fooled": there
are
`w ≠ w'` such that `A` accepts `mixedWord w w'` whenever it accepts `mixedWord w w`.  Proof: for
the run on `mixedWord w w` with blocks of length `n`, step 2A gives an unvisited block `i0 n w` (the
positions of the left and right copy of block `i` are `[i (n+1), i (n+1) + n)` and
`[(2m-1-i)(n+1), (2m-1-i)(n+1) + n)`); step 2C gives `w ≠ w'` differing only in this block with the
same protocols; steps 2D2 and 2B1 give the layout and step 2B the cut and paste. -/
private lemma not_isRecognizedBy_palindromeBlocks_step2D_glue {k m : ℕ} (hmk : k.choose 2 < m)
    {Q : Type} [Finite Q] (A : MultiheadAutomaton k BlockSymbol Q) :
    ∃ w w' : Fin m → List Bool, w ≠ w' ∧
      (A.Accepts (mixedWord w w) → A.Accepts (mixedWord w w')) := by
  classical
  cases nonempty_fintype Q
  -- for every `n` and `w` some block is not visited by a pair of heads
  have hex : ∀ (n : ℕ) (w : Fin m → List Bool), ∃ i : Fin m, ¬ ∃ (t : ℕ) (x y : Fin k),
      (i : ℕ) * (n + 1) ≤ (A.run (mixedWord w w) t).pos x ∧
      (A.run (mixedWord w w) t).pos x < (i : ℕ) * (n + 1) + n ∧
      (2 * m - 1 - (i : ℕ)) * (n + 1) ≤ (A.run (mixedWord w w) t).pos y ∧
      (A.run (mixedWord w w) t).pos y < (2 * m - 1 - (i : ℕ)) * (n + 1) + n := by
    intro n w
    by_contra hcon
    push Not at hcon
    have h2A := not_isRecognizedBy_palindromeBlocks_step2A_pairCounting
      (fun t x => (A.run (mixedWord w w) t).pos x)
      (fun t x => not_isRecognizedBy_palindromeBlocks_step2D0_pos_succ A _ t x)
      (fun i : Fin m => (i : ℕ) * (n + 1)) (fun i : Fin m => (i : ℕ) * (n + 1) + n)
      (fun i : Fin m => (2 * m - 1 - (i : ℕ)) * (n + 1))
      (fun i : Fin m => (2 * m - 1 - (i : ℕ)) * (n + 1) + n)
      (by
        intro i j hij
        have h1 : (i : ℕ) + 1 ≤ j := hij
        have h2 := Nat.mul_le_mul_right (n + 1) h1
        change (i : ℕ) * (n + 1) + n ≤ (j : ℕ) * (n + 1)
        nlinarith [h2])
      (by
        intro i j hij
        have h1 : (i : ℕ) < j := hij
        have hj := j.isLt
        have h3 : 2 * m - 1 - (j : ℕ) + 1 ≤ 2 * m - 1 - (i : ℕ) := by omega
        have h2 := Nat.mul_le_mul_right (n + 1) h3
        change (2 * m - 1 - (j : ℕ)) * (n + 1) + n ≤ (2 * m - 1 - (i : ℕ)) * (n + 1)
        nlinarith [h2])
      (by
        intro i j
        have hi := i.isLt
        have hj := j.isLt
        have h3 : (i : ℕ) + 1 ≤ 2 * m - 1 - (j : ℕ) := by omega
        have h2 := Nat.mul_le_mul_right (n + 1) h3
        change (i : ℕ) * (n + 1) + n ≤ (2 * m - 1 - (j : ℕ)) * (n + 1)
        nlinarith [h2])
      Finset.univ (fun i _ => hcon i)
    simp only [Finset.card_univ, Fintype.card_fin] at h2A
    omega
  choose i0 hi0 using hex
  let E : ℕ → (Fin m → List Bool) → ℕ → HeadConfig k Q := fun n w l =>
    A.run (mixedWord w w) (levelTime A (mixedWord w w) ((i0 n w : ℕ) * (n + 1))
      ((i0 n w : ℕ) * (n + 1) + n) ((2 * m - 1 - (i0 n w : ℕ)) * (n + 1))
      ((2 * m - 1 - (i0 n w : ℕ)) * (n + 1) + n) l)
  have hEb : ∀ n w l, (∀ j, (w j).length = n) → ∀ x, (E n w l).pos x ≤ 2 * m * n + 2 * m := by
    intro n w l hw x
    exact (MultiheadAutomaton.pos_le_length A _ _ x).trans
      (not_isRecognizedBy_palindromeBlocks_step2D4_length w w hw hw)
  obtain ⟨n, w, w', hw, hw', hne, hi, hag, hEq⟩ :=
    not_isRecognizedBy_palindromeBlocks_step2C_pigeonhole i0 E hEb
  refine ⟨w, w', hne, ?_⟩
  obtain ⟨pre, mid, post, hpre, hmid, hu, hu', hh⟩ :=
    not_isRecognizedBy_palindromeBlocks_step2D2_decomp n (i0 n w) w w' hw hag
  have hno := hi0 n w
  have hEq' : ∀ l ≤ 4 * k, E n w l = E n w' l := hEq
  generalize hi_def : i0 n w = i at hpre hmid hu hu' hh hno hag hEq' hi
  have hXlen : ((w i).map BlockSymbol.bit).length = n := by simp [hw i]
  have hYlen : ((w' i).map BlockSymbol.bit).length = n := by simp [hw' i]
  have hr : 2 * m - 1 - (i : ℕ) = i + 1 + 2 * (m - 1 - i) := by have := i.isLt; omega
  have ha : (i : ℕ) * (n + 1) = pre.length := hpre.symm
  have hb : (i : ℕ) * (n + 1) + n = (i : ℕ) * (n + 1) + ((w i).map BlockSymbol.bit).length := by
    rw [hXlen]
  have hc : (2 * m - 1 - (i : ℕ)) * (n + 1) = ((i : ℕ) * (n + 1) + n) + mid.length := by
    rw [hmid, hr]; ring
  have hd : (2 * m - 1 - (i : ℕ)) * (n + 1) + n =
      (2 * m - 1 - (i : ℕ)) * (n + 1) + ((w i).map BlockSymbol.bit).length := by
    rw [hXlen]
  obtain ⟨hz0, hz1, hz3, hdlen, hlen'⟩ := not_isRecognizedBy_palindromeBlocks_step2B1_zones
    pre mid post ((w i).map BlockSymbol.bit) ((w' i).map BlockSymbol.bit) (by rw [hXlen, hYlen])
    _ _ _ _ ha hb hc hd
  simp only [← hu, ← hu', ← hh] at hz0 hz1 hz3 hdlen hlen'
  refine not_isRecognizedBy_palindromeBlocks_step2B_cutAndPaste A (mixedWord w w)
    (mixedWord w' w') (mixedWord w w') ((i : ℕ) * (n + 1)) ((i : ℕ) * (n + 1) + n)
    ((2 * m - 1 - (i : ℕ)) * (n + 1)) ((2 * m - 1 - (i : ℕ)) * (n + 1) + n) (by omega)
    (by omega) (by omega) hdlen hlen' hz0 hz1 hz3 hno ?_
  intro l hl
  have h1 := hEq' l hl
  simp only [E] at h1
  rw [hi_def, ← hi] at h1
  exact h1

/-- **SUV p. 237.**  A `k`-head automaton does not recognize `L_m` when `m > k(k-1)/2`.  This is
where incompressible blocks and cutting and pasting computations are used. -/
theorem not_isRecognizedBy_palindromeBlocks {k m : ℕ} (hmk : k.choose 2 < m) :
    ¬ IsRecognizedBy k (palindromeBlocks m) := by
  rintro ⟨Q, hQ, A, hA⟩
  obtain ⟨w, w', hne, hfool⟩ := not_isRecognizedBy_palindromeBlocks_step2D_glue hmk A
  have hacc : A.Accepts (mixedWord w w) :=
    (hA _).mp ((not_isRecognizedBy_palindromeBlocks_inj w w).mpr rfl)
  have hmem : mixedWord w w' ∈ palindromeBlocks m := (hA _).mpr (hfool hacc)
  exact hne ((not_isRecognizedBy_palindromeBlocks_inj w w').mp hmem)


private lemma exists_language_isRecognizedBy_succ_not_k_zero :
    ¬ IsRecognizedBy 0 ({[]} : Set (List BlockSymbol)) := by
  rintro ⟨Q, _, A, hA⟩
  have hrun : ∀ (w : List BlockSymbol) (t : ℕ), A.run w t = A.start := by
    intro w t
    induction t with
    | zero => rfl
    | succ t ih =>
      have h : A.run w (t + 1) = A.next w (A.run w t) := Function.iterate_succ_apply' _ _ _
      rw [h, ih, MultiheadAutomaton.next,
        ite_eq_left (show MultiheadAutomaton.Terminated w A.start from fun i => i.elim0)]
  have hacc : ∀ w : List BlockSymbol, A.Accepts w ↔ A.init ∈ A.accepting := by
    intro w
    constructor
    · rintro ⟨t, -, ht⟩
      rw [hrun] at ht
      exact ht
    · intro h
      exact ⟨0, fun i => i.elim0, by rw [hrun]; exact h⟩
  have h1 : A.init ∈ A.accepting := (hacc []).mp ((hA []).mp rfl)
  have h2 := (hA [BlockSymbol.sep]).mpr ((hacc _).mpr h1)
  simp at h2

/-- The one-head automaton accepting only the empty word: the state records that the head has seen
only the end marker. -/
private def exists_language_isRecognizedBy_succ_not_k_zero_succ_aut :
    MultiheadAutomaton 1 BlockSymbol Bool where
  init := true
  accepting := {true}
  step := fun q obs => (q && decide (obs 0 = none), {0})
  moves_nonempty := by
    intro q obs h
    obtain ⟨i, hi⟩ := h
    refine ⟨i, ?_, hi⟩
    have : i = 0 := Subsingleton.elim _ _
    simp [this]

private lemma exists_language_isRecognizedBy_succ_not_k_zero_succ_state_false
    (a : BlockSymbol) (l : List BlockSymbol) (t : ℕ) :
    ((exists_language_isRecognizedBy_succ_not_k_zero_succ_aut.run (a :: l) (t + 1)).state)
      = false := by
  set A := exists_language_isRecognizedBy_succ_not_k_zero_succ_aut with hA
  induction t with
  | zero =>
    have hrun : A.run (a :: l) 1 = A.next (a :: l) A.start := by
      simp [MultiheadAutomaton.run]
    rw [hrun]
    have hnt : ¬ MultiheadAutomaton.Terminated (a :: l) A.start := by
      intro h
      have := h 0
      simp [MultiheadAutomaton.observe, MultiheadAutomaton.start] at this
    unfold MultiheadAutomaton.next
    rw [ite_eq_right hnt]
    simp [hA, exists_language_isRecognizedBy_succ_not_k_zero_succ_aut,
      MultiheadAutomaton.observe, MultiheadAutomaton.start]
  | succ t ih =>
    have hrun : A.run (a :: l) (t + 1 + 1) = A.next (a :: l) (A.run (a :: l) (t + 1)) :=
      Function.iterate_succ_apply' _ _ _
    rw [hrun]
    unfold MultiheadAutomaton.next
    split_ifs with hterm
    · exact ih
    · change (_ && _ : Bool) = false
      rw [ih]
      rfl

private lemma exists_language_isRecognizedBy_succ_not_k_zero_succ :
    IsRecognizedBy 1 ({[]} : Set (List BlockSymbol)) := by
  refine ⟨Bool, inferInstance, exists_language_isRecognizedBy_succ_not_k_zero_succ_aut, ?_⟩
  intro w
  cases w with
  | nil =>
    simp only [Set.mem_singleton_iff, true_iff]
    refine ⟨0, ?_, ?_⟩
    · intro i
      simp [MultiheadAutomaton.observe]
    · simp [MultiheadAutomaton.run, MultiheadAutomaton.start,
        exists_language_isRecognizedBy_succ_not_k_zero_succ_aut]
  | cons a l =>
    simp only [Set.mem_singleton_iff, List.cons_ne_nil, false_iff]
    rintro ⟨t, hterm, hacc⟩
    cases t with
    | zero =>
      have := hterm 0
      simp [MultiheadAutomaton.run, MultiheadAutomaton.start, MultiheadAutomaton.observe] at this
    | succ t =>
      have h := exists_language_isRecognizedBy_succ_not_k_zero_succ_state_false a l t
      rw [h] at hacc
      simp [exists_language_isRecognizedBy_succ_not_k_zero_succ_aut] at hacc

/-- **SUV Theorem 154, p. 236.**  For every `k` there is a language recognized by a `(k + 1)`-head
automaton and not by a `k`-head one.  For `k ≥ 1` this is `L_m` with `m = (k + 1) k / 2`.  For
`k = 0` the book's languages do not apply, as `(0 + 1) 0 / 2 = 0`; a `0`-head automaton accepts
everything or nothing, and `L = {Λ}` is recognized by one head. -/
theorem exists_language_isRecognizedBy_succ_not (k : ℕ) :
    ∃ L : Set (List BlockSymbol), IsRecognizedBy (k + 1) L ∧ ¬ IsRecognizedBy k L := by
  cases k with
  | zero =>
    use {[]}
    exact ⟨exists_language_isRecognizedBy_succ_not_k_zero_succ,
      exists_language_isRecognizedBy_succ_not_k_zero⟩
  | succ k =>
    use palindromeBlocks ((k + 2).choose 2)
    have h1 : 1 ≤ (k + 2).choose 2 := Nat.succ_le_of_lt (Nat.choose_pos (by omega))
    have h2 : (k + 1).choose 2 < (k + 2).choose 2 := by
      have h_eq : (k + 2).choose 2 = (k + 1).choose 2 + (k + 1) := by
        calc (k + 2).choose 2
          _ = (k + 1 + 1).choose (1 + 1) := rfl
          _ = (k + 1).choose (1 + 1) + (k + 1).choose 1 := by rw [Nat.choose, add_comm]
          _ = (k + 1).choose 2 + (k + 1) := by rw [Nat.choose_one_right]
      omega
    exact ⟨isRecognizedBy_palindromeBlocks h1 le_rfl, not_isRecognizedBy_palindromeBlocks h2⟩

end Kolmogorov.Applications
