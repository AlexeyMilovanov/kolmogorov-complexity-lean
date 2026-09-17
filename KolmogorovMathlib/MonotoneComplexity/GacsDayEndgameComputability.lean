import KolmogorovMathlib.MonotoneComplexity.GacsDayAccumulation

/-!
# Computability and branching bookkeeping for the sequential endgame

The sequential round composition of SUV pp. 138, 142, 144 needs three pieces of
infrastructure that are independent of the construction itself:

* `computable_grayScaleLadder`: the ladder of scales along which the rounds are
  run is jointly computable in the stage, the two depths and the round index;
* `computable₂_liftFamilyStrategy`: planting a computable family of family
  strategies below the root children is a computable operation, uniformly in the
  round index;
* `branching_grayScaleLadder_le`: the branching envelope of
  `GrayFamilyUniformInductionStatement`, evaluated along the ladder, stays below
  a single power of two.

None of these lemmas assume anything about the winning conditions; they are pure
bookkeeping about the data of the induction.
-/

namespace Kolmogorov

/-! ## The scale ladder is jointly computable -/

/-- The gray scale ladder is the iteration of the depth increment, written as a `Nat.rec`. -/
lemma grayScaleLadder_eq_rec (deltaDepth : ℕ → ℕ → ℕ → ℕ) (k a e j : ℕ) :
    grayScaleLadder deltaDepth k a e j =
      Nat.rec e (fun _ IH => deltaDepth k a IH) j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [grayScaleLadder_succ, ih]

/-- The whole scale ladder is computable jointly in the amplification stage, the
two dyadic depths and the round index. -/
lemma computable_grayScaleLadder
    (deltaDepth : ℕ → ℕ → ℕ → ℕ)
    (hd : GrayNat3Computable deltaDepth) :
    Computable (fun p : (ℕ × ℕ × ℕ) × ℕ =>
      grayScaleLadder deltaDepth p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have hd' : Computable (fun p : ℕ × ℕ × ℕ => deltaDepth p.1 p.2.1 p.2.2) := hd
  have h1 : Computable (fun r : ((ℕ × ℕ × ℕ) × ℕ) × (ℕ × ℕ) => r.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have h2 : Computable (fun r : ((ℕ × ℕ × ℕ) × ℕ) × (ℕ × ℕ) => r.1.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have h3 : Computable (fun r : ((ℕ × ℕ × ℕ) × ℕ) × (ℕ × ℕ) => r.2.2) :=
    Computable.snd.comp Computable.snd
  have hpair : Computable (fun r : ((ℕ × ℕ × ℕ) × ℕ) × (ℕ × ℕ) =>
      ((r.1.1.1, r.1.1.2.1, r.2.2) : ℕ × ℕ × ℕ)) := h1.pair (h2.pair h3)
  have hcomp := hd'.comp hpair
  have hstep : Computable₂ (fun (p : (ℕ × ℕ × ℕ) × ℕ) (q : ℕ × ℕ) =>
      deltaDepth p.1.1 p.1.2.1 q.2) := hcomp
  have hf : Computable (fun p : (ℕ × ℕ × ℕ) × ℕ => p.2) := Computable.snd
  have hg : Computable (fun p : (ℕ × ℕ × ℕ) × ℕ => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hrec := Computable.nat_rec hf hg hstep
  refine hrec.of_eq ?_
  rintro ⟨⟨k, a, e⟩, j⟩
  exact (grayScaleLadder_eq_rec deltaDepth k a e j).symm

/-! ## The branching envelope along the ladder -/

/-- Combining the additive depth envelope with the branching envelope of
`GrayFamilyUniformInductionStatement`: along the whole ladder the branching factor
stays below one power of two whose exponent grows linearly in the number of
rounds. -/
lemma branching_grayScaleLadder_le
    (deltaDepth branching : ℕ → ℕ → ℕ → ℕ) (k a e E : ℕ)
    (hE : ∀ x, deltaDepth k a x ≤ x + E)
    (hb : ∀ x, branching k a x ≤ max (2 * 2 ^ (x - a)) (2 ^ E)) (j : ℕ) :
    branching k a (grayScaleLadder deltaDepth k a e j) ≤
      2 ^ (1 + e + (j + 1) * E) := by
  set x := grayScaleLadder deltaDepth k a e j with hx
  have hxle : x ≤ e + j * E := grayScaleLadder_le_add_mul deltaDepth k a e E hE j
  have h1 : 2 * (2 : ℕ) ^ (x - a) ≤ 2 ^ (1 + e + (j + 1) * E) := by
    rw [show 2 * 2 ^ (x - a) = 2 ^ ((x - a) + 1) by
      rw [pow_succ, Nat.mul_comm]]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have : x - a ≤ x := Nat.sub_le _ _
    have hmul : j * E ≤ (j + 1) * E := Nat.mul_le_mul_right E (Nat.le_succ j)
    omega
  have h2 : (2 : ℕ) ^ E ≤ 2 ^ (1 + e + (j + 1) * E) := by
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have : E ≤ (j + 1) * E := Nat.le_mul_of_pos_left E (Nat.succ_pos j)
    omega
  exact le_trans (hb x) (max_le h1 h2)

/-! ## Planting a computable family of family strategies is computable -/

/-- Reading a list back through `List.ofFn` and its indices recovers the mapped list. -/
lemma list_ofFn_getD_eq_map {α β : Type} [Inhabited α] (l : List α) (f : α → β) (d : α) :
    (List.ofFn fun i : Fin l.length => f (l.getD i d)) = l.map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD]

/-- `List.ofFn` on a function of the index value is the map of that function over `List.range n`. -/
lemma list_ofFn_val_eq_map_range {β : Type} (n : ℕ) (g : ℕ → β) :
    (List.ofFn fun j : Fin n => g j.val) = (List.range n).map g := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

/-- The server move seen below child `i` collects the entries whose key starts with `i`, with
that first entry removed. -/
lemma serverMoveBelow_eq_flatMap (i : ℕ) (m : ServerMove) :
    serverMoveBelow i m =
      m.flatMap (fun p =>
        match p.1 with
        | [] => []
        | j :: z => if j = i then [(z, p.2)] else []) := by
  induction m with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, a⟩ := p
    cases y with
    | nil => simpa [serverMoveBelow] using ih
    | cons j z =>
      by_cases hj : j = i <;>
        simp only [serverMoveBelow, List.filterMap_cons, List.flatMap_cons, hj,
          if_true, if_false] <;>
        simp only [serverMoveBelow] at ih <;> simp [ih]

/-- Restricting a server move below a child is primitive recursive. -/
lemma primrec_serverMoveBelow :
    Primrec (fun q : ℕ × ServerMove => serverMoveBelow q.1 q.2) := by
  have hf : Primrec (fun q : (ℕ × ServerMove) × (GacsDayNode × Allocation) => q.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hg : Primrec (fun _ : (ℕ × ServerMove) × (GacsDayNode × Allocation) =>
    ([] : ServerMove)) := Primrec.const []
  have hh : Primrec₂ (fun (q : (ℕ × ServerMove) × (GacsDayNode × Allocation))
      (jz : ℕ × List ℕ) => if jz.1 = q.1.1 then [(jz.2, q.2.2)] else ([] : ServerMove)) := by
    have hcond : PrimrecPred
        (fun r : ((ℕ × ServerMove) × (GacsDayNode × Allocation)) × (ℕ × List ℕ) =>
          r.2.1 = r.1.1.1) :=
      PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hthen : Primrec (fun r : ((ℕ × ServerMove) × (GacsDayNode × Allocation)) × (ℕ × List ℕ) =>
        [(r.2.2, r.1.2.2)]) :=
      Primrec.list_cons.comp (Primrec.pair (Primrec.snd.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) (Primrec.const [])
    exact Primrec.ite hcond hthen (Primrec.const [])
  have hcases := Primrec.list_casesOn hf hg hh
  have hinner : Primrec₂ (fun (a : ℕ × ServerMove) (p : GacsDayNode × Allocation) =>
      match p.1 with
      | [] => ([] : ServerMove)
      | j :: z => if j = a.1 then [(z, p.2)] else []) := by
    refine hcases.of_eq ?_
    rintro ⟨a, y, alloc⟩
    cases y <;> rfl
  have hmain := Primrec.list_flatMap (f := fun a : ℕ × ServerMove => a.2) Primrec.snd hinner
  refine hmain.of_eq ?_
  rintro ⟨i, m⟩
  exact (serverMoveBelow_eq_flatMap i m).symm

/-- One server move of the big tree, read as one family server move of its first `n`
root subtrees. -/
def serverMoveFamilyBelow (n : ℕ) (m : ServerMove) : FamilyServerMove :=
  (List.range n).map (fun j => serverMoveBelow j m)

/-- The family of moves seen below the roots at time `t` is the restriction of the move at time
`t`. -/
lemma familyServerMovesBelow_eq (n : ℕ) (sm : ℕ → ServerMove) (t : ℕ) :
    familyServerMovesBelow n sm t = serverMoveFamilyBelow n (sm t) := by
  simp only [familyServerMovesBelow, serverMoveFamilyBelow]
  exact list_ofFn_val_eq_map_range n (fun j => serverMoveBelow j (sm t))

/-- Splitting a server move into the moves below the first `n` children is primitive recursive. -/
lemma primrec_serverMoveFamilyBelow :
    Primrec (fun q : ℕ × ServerMove => serverMoveFamilyBelow q.1 q.2) := by
  have hrange : Primrec (fun q : ℕ × ServerMove => List.range q.1) :=
    Primrec.list_range.comp Primrec.fst
  have hg : Primrec₂ (fun (q : ℕ × ServerMove) (j : ℕ) => serverMoveBelow j q.2) :=
    primrec_serverMoveBelow.comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))
  exact Primrec.list_map hrange hg

/-- Splitting a whole list of server moves into families is primitive recursive. -/
lemma primrec_map_serverMoveFamilyBelow :
    Primrec (fun q : ℕ × List ServerMove => q.2.map (serverMoveFamilyBelow q.1)) := by
  have hg : Primrec₂ (fun (q : ℕ × List ServerMove) (m : ServerMove) =>
      serverMoveFamilyBelow q.1 m) :=
    primrec_serverMoveFamilyBelow.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact Primrec.list_map Primrec.snd hg

/-- Lifting a family client move to a single move at scale `r` is primitive recursive. -/
lemma primrec_clientMoveLift :
    Primrec (fun q : (ℕ × ℚ) × FamilyClientMove => clientMoveLift q.1.1 q.1.2 q.2) := by
  have hrange : Primrec (fun q : (ℕ × ℚ) × FamilyClientMove => List.range q.1.1) :=
    Primrec.list_range.comp (Primrec.fst.comp Primrec.fst)
  have hinner : Primrec₂ (fun (a : ((ℕ × ℚ) × FamilyClientMove) × ℕ)
      (p : GacsDayNode × ℚ) => ((a.2 :: p.1 : GacsDayNode), p.2)) :=
    Primrec.pair (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
  have hlist : Primrec (fun a : ((ℕ × ℚ) × FamilyClientMove) × ℕ =>
      familyClientMoveAt a.1.2 a.2) :=
    (Primrec.list_getD ([] : ClientMove)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hg : Primrec₂ (fun (q : (ℕ × ℚ) × FamilyClientMove) (i : ℕ) =>
      (familyClientMoveAt q.2 i).map (fun p => ((i :: p.1 : GacsDayNode), p.2))) :=
    Primrec.list_map hlist hinner
  have hflat := Primrec.list_flatMap hrange hg
  have hcons := Primrec.list_cons.comp
    (Primrec.pair (Primrec.const ([] : GacsDayNode)) (Primrec.snd.comp Primrec.fst)) hflat
  refine hcons.of_eq ?_
  rintro ⟨⟨n, r⟩, fcm⟩
  rfl

/-- Self-play of a family strategy, now also uniform in the unavailable set and the
family size. -/
lemma computable₂_familySelfPlay_param {A : ℕ → Allocation} {n : ℕ → ℕ}
    {σ' : ℕ → ClientFamilyStrategy}
    (h : Computable₂ (fun (d : ℕ) (p : FamilyGameHistory) => σ' d (A d) (n d) p)) :
    Computable₂ (fun d ss => familySelfPlay (A d) (n d) (σ' d) ss) := by
  have hstep : Computable₂ (fun (a : ℕ × List FamilyServerMove) (p : ℕ × List FamilyClientMove) =>
      p.2 ++ [σ' a.1 (A a.1) (n a.1) (p.2, a.2.take p.1)]) := by
    have hσ : Computable (fun q : (ℕ × List FamilyServerMove) × (ℕ × List FamilyClientMove) =>
        σ' q.1.1 (A q.1.1) (n q.1.1) (q.2.2, q.1.2.take q.2.1)) :=
      h.comp (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.snd.comp Computable.snd)
        (Primrec.list_take.to_comp.comp
          (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.fst)))
    exact Computable.list_concat.comp (Computable.snd.comp Computable.snd) hσ
  have hrec := Computable.nat_rec (f := fun a : ℕ × List FamilyServerMove => a.2.length)
    (g := fun _ : ℕ × List FamilyServerMove => ([] : List FamilyClientMove))
    (Computable.list_length.comp Computable.snd) (Computable.const _) hstep
  refine hrec.of_eq ?_
  rintro ⟨d, ss⟩
  exact (familySelfPlayAux_eq_rec _ _ _ _ _).symm

/-- The lifted strategy recomputes the family play from the server part of the
history, so it can be written as a single application of the family strategy to a
self-play history. -/
lemma liftFamilyStrategy_eq_selfPlay (n : ℕ) (r : ℚ) (σf : ClientFamilyStrategy)
    (hist : GameHistory) :
    liftFamilyStrategy n r σf hist =
      clientMoveLift n r
        (σf [] n (familySelfPlay [] n σf (hist.2.map (serverMoveFamilyBelow n)),
          hist.2.map (serverMoveFamilyBelow n))) := by
  unfold liftFamilyStrategy
  rw [playClientFamily_eq_selfPlay]
  have hss : (List.ofFn fun i : Fin hist.2.length =>
      familyServerMovesBelow n (fun s => hist.2.getD s []) i.val)
      = hist.2.map (serverMoveFamilyBelow n) := by
    refine Eq.trans ?_ (list_ofFn_getD_eq_map hist.2 (serverMoveFamilyBelow n) ([] : ServerMove))
    congr 1
    funext i
    exact familyServerMovesBelow_eq n (fun s => hist.2.getD s []) i.val
  rw [hss]

/-- Planting a computable family of family strategies below the root children of one
big tree is a computable operation, uniformly in the round index. -/
lemma computable₂_liftFamilyStrategy
    (n : ℕ → ℕ) (r : ℕ → ℚ)
    (σf : ℕ → ClientFamilyStrategy)
    (hn : Computable n) (hr : Computable r)
    (hσ : Computable
      (fun p : ℕ × (Allocation × (ℕ × FamilyGameHistory)) =>
        σf p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable₂ (fun d => liftFamilyStrategy (n d) (r d) (σf d)) := by
  have harg : Computable (fun q : ℕ × FamilyGameHistory =>
      ((q.1, (([] : Allocation), ((n q.1, q.2) : ℕ × FamilyGameHistory))) :
        ℕ × (Allocation × (ℕ × FamilyGameHistory)))) :=
    Computable.pair Computable.fst
      (Computable.pair (Computable.const [])
        (Computable.pair (hn.comp Computable.fst) Computable.snd))
  have hcurry := hσ.comp harg
  have hσ' : Computable₂ (fun (d : ℕ) (p : FamilyGameHistory) => σf d [] (n d) p) := hcurry
  have hself := computable₂_familySelfPlay_param (A := fun _ : ℕ => ([] : Allocation)) hσ'
  have hss : Computable (fun q : ℕ × GameHistory =>
      q.2.2.map (serverMoveFamilyBelow (n q.1))) := by
    have := primrec_map_serverMoveFamilyBelow.to_comp.comp
      (Computable.pair (hn.comp Computable.fst)
        (Computable.snd.comp (Computable.snd (α := ℕ) (β := GameHistory))))
    exact this
  have hplay : Computable (fun q : ℕ × GameHistory =>
      familySelfPlay [] (n q.1) (σf q.1) (q.2.2.map (serverMoveFamilyBelow (n q.1)))) :=
    hself.comp Computable.fst hss
  have hmove := hσ'.comp Computable.fst (Computable.pair hplay hss)
  have hpar : Computable (fun q : ℕ × GameHistory => ((n q.1, r q.1) : ℕ × ℚ)) :=
    Computable.pair (hn.comp Computable.fst) (hr.comp Computable.fst)
  have hfinal := primrec_clientMoveLift.to_comp.comp (Computable.pair hpar hmove)
  refine hfinal.of_eq ?_
  rintro ⟨d, hist⟩
  exact (liftFamilyStrategy_eq_selfPlay (n d) (r d) (σf d) hist).symm

/-- The form the sequential endgame needs: a computable uniform family strategy
scheme, evaluated at computable round parameters and planted below the root
children, gives a computable single-tree strategy uniformly in the round index. -/
lemma computable₂_liftFamilyStrategy_scheme
    (k a e n : ℕ → ℕ) (r : ℕ → ℚ) (σ : UniformFamilyStrategyScheme)
    (hk : Computable k) (ha : Computable a) (he : Computable e)
    (hn : Computable n) (hr : Computable r)
    (hσ : UniformFamilyStrategySchemeComputable σ) :
    Computable₂ (fun d => liftFamilyStrategy (n d) (r d) (σ (k d) (a d) (e d))) := by
  have hσ' : Computable
      (fun p : (ℕ × ℕ × ℕ) × (Allocation × (ℕ × FamilyGameHistory)) =>
        σ p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2.1 p.2.2.2) := hσ
  have harg : Computable (fun p : ℕ × (Allocation × (ℕ × FamilyGameHistory)) =>
      (((k p.1, a p.1, e p.1) : ℕ × ℕ × ℕ), p.2)) :=
    Computable.pair
      (Computable.pair (hk.comp Computable.fst)
        (Computable.pair (ha.comp Computable.fst) (he.comp Computable.fst)))
      Computable.snd
  have hcomp := hσ'.comp harg
  exact computable₂_liftFamilyStrategy n r (fun d => σ (k d) (a d) (e d)) hn hr hcomp

end Kolmogorov
