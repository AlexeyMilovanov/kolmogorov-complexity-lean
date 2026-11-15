import KolmogorovMathlib.InformationLogic.SingletonFormulas.PeirceLogBound

/-!
# Peirce Complexity

Complexity of the singleton Peirce formula `(x → y) → x` in the problem calculus.  The main
declarations are `problemK_peirce_singleton_le_log_complexity` (Problem 341: the `O(log n)` error
term of Theorem 239 can be replaced by `O(log m)`, `m = max (C(x), C(y))`),
`plainK_le_problemK_imp_imp_singleton` and `problemK_imp_imp_singleton_le_plainK` (the two
inequalities giving `C((x → y) → x) = C(x) + O(log n)`), and `problemK_imp_imp_singleton_le_disj`
(Theorem 240, first inequality).  The auxiliary private lemmas build the two-point modifications
of a map, the family of programs computing them, and the dovetailed search for compatible pairs.
This formalizes part of Section 13.3 of the book by Shen, Uspensky and Vereshchagin,
"Kolmogorov complexity and algorithmic randomness".
-/

namespace Kolmogorov
namespace InformationLogic
open ProblemCalculus

/-- The two-point modification `τ` used in the proof of Problem 341: `τ(c) = d`, and `τ(a) = b`
when `a ≠ c`; the value is `[]` elsewhere. -/
private def problemK_peirce_singleton_le_log_complexity_tau (c d a b w : BitString) : BitString :=
  if w = c then d else if w = a then b else []

/-- `(a, b) ∈ S × S` (`S` = strings of length at most `m`) is *compatible* with the program `p`
(relative to the family of programs `ℓ m c d a b` computing `l_τ` for the two-point maps `τ`):
for all `(c, d) ∈ S × S` with `τ(a) = b` (that is, `c = a → d = b`), `[p](l_τ) = D(a)`. -/
private def problemK_peirce_singleton_le_log_complexity_compat (D : Map) (P : ProblemCalculus)
    (ℓ : ℕ → BitString → BitString → BitString → BitString → BitString) (m : ℕ)
    (p a b : BitString) : Prop :=
  a.length ≤ m ∧ b.length ≤ m ∧ ∀ c d : BitString, c.length ≤ m → d.length ≤ m →
    (c = a → d = b) → ∃ v, v ∈ P.lang (p, ℓ m c d a b) ∧ v ∈ D (a, [])

/-- The two-point map `τ` is primitive recursive in `(c, d, a, b, w)`. -/
private theorem problemK_peirce_singleton_le_log_complexity_programs_tau_primrec :
    Primrec (fun q : BitString × BitString × BitString × BitString × BitString =>
      problemK_peirce_singleton_le_log_complexity_tau q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  unfold problemK_peirce_singleton_le_log_complexity_tau
  have hc : Primrec (fun q : BitString × BitString × BitString × BitString × BitString => q.1) :=
    Primrec.fst
  have hd : Primrec (fun q : BitString × BitString × BitString × BitString × BitString => q.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ha : Primrec
      (fun q : BitString × BitString × BitString × BitString × BitString => q.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec
      (fun q : BitString × BitString × BitString × BitString × BitString => q.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hw : Primrec
      (fun q : BitString × BitString × BitString × BitString × BitString => q.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.ite (Primrec.eq.comp hw hc) hd
    (Primrec.ite (Primrec.eq.comp hw ha) hb (Primrec.const []))

/-- Generic dovetailed search (copy of the argument of `DiagonalLowerBounds`): for a partial
computable `G a b` there is a partial computable `H a` whose values are values of some `G a b`
and which is defined as soon as some `G a b` is. -/
private theorem problemK_peirce_singleton_le_log_complexity_programs_search
    {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ] (G : α → β →. γ)
    (hG : Partrec (fun z : α × β => G z.1 z.2)) :
    ∃ H : α →. γ, Partrec H ∧ (∀ a c, c ∈ H a → ∃ b, c ∈ G a b) ∧
      (∀ a b, (G a b).Dom → (H a).Dom) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hG
  let f : α → ℕ → Option γ := fun a n =>
    (Encodable.decode (α := β) n.unpair.1).bind fun b =>
      (Nat.Partrec.Code.evaln n.unpair.2 c (Encodable.encode (a, b))).bind
        (Encodable.decode (α := γ))
  have hf : Computable₂ f := by
    have h1 : Computable (fun p : α × ℕ => Encodable.decode (α := β) p.2.unpair.1) :=
      Computable.comp Computable.decode
        (Computable.comp Computable.fst (Computable.comp Computable.unpair Computable.snd))
    have h2 : Computable₂ (fun (p : α × ℕ) (b : β) =>
        Nat.Partrec.Code.evaln p.2.unpair.2 c (Encodable.encode (p.1, b))) := by
      have h_steps : Computable (fun q : (α × ℕ) × β => q.1.2.unpair.2) :=
        Primrec.to_comp
          (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))
      have h_input : Computable (fun q : (α × ℕ) × β => Encodable.encode (q.1.1, q.2)) :=
        Computable.comp Computable.encode
          (Primrec.to_comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
      have hev : Primrec (fun q : (ℕ × Nat.Partrec.Code) × ℕ =>
          Nat.Partrec.Code.evaln q.1.1 q.1.2 q.2) := Nat.Partrec.Code.primrec_evaln
      exact (hev.to_comp).comp
        (Computable.pair (Computable.pair h_steps (Computable.const c)) h_input)
    have h3 : Computable₂ (fun (q : (α × ℕ) × β) (m : ℕ) => Encodable.decode (α := γ) m) :=
      (Computable.decode.comp Computable.snd).to₂
    have h4 : Computable₂ (fun (p : α × ℕ) (b : β) =>
        (Nat.Partrec.Code.evaln p.2.unpair.2 c (Encodable.encode (p.1, b))).bind
          (Encodable.decode (α := γ))) :=
      Computable.option_bind h2 h3
    exact Computable.option_bind h1 h4
  refine ⟨fun a => Nat.rfindOpt (f a), Partrec.rfindOpt hf, ?_, ?_⟩
  · intro a c' hc'
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hc'
    simp only [f, Option.mem_def, Option.bind_eq_some_iff] at hn
    obtain ⟨b, hb, m, hm, hdec⟩ := hn
    refine ⟨b, ?_⟩
    have hev : m ∈ (G a b).map (Encodable.encode : γ → ℕ) := by
      have h := Nat.Partrec.Code.evaln_sound hm
      rw [hc] at h
      simpa using h
    obtain ⟨c'', hc'', rfl⟩ := Part.mem_map_iff _ |>.1 hev
    rw [Encodable.encodek] at hdec
    obtain rfl := Option.some.inj hdec
    exact hc''
  · intro a b hdom
    obtain ⟨c'', hc''⟩ := Part.dom_iff_mem.1 hdom
    have hm : Encodable.encode c'' ∈ (G a b).map (Encodable.encode : γ → ℕ) :=
      Part.mem_map _ hc''
    have hev : Encodable.encode c'' ∈ Nat.Partrec.Code.eval c (Encodable.encode (a, b)) := by
      rw [hc]
      simpa using hm
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.1 hev
    rw [Nat.rfindOpt_dom]
    refine ⟨Nat.pair (Encodable.encode b) k, c'', ?_⟩
    rw [Option.mem_def] at hk ⊢
    simp only [f, Nat.unpair_pair, Encodable.encodek, Option.bind_some]
    rw [hk]
    simp

/-- The search for a program of length at most `m` producing `u`: a partial computable
`A (m, u)` defined whenever such a program exists, all of whose values are such programs. -/
private theorem problemK_peirce_singleton_le_log_complexity_programs_find (D : Map)
    (hD : Partrec D) :
    ∃ A : ℕ × BitString →. BitString, Partrec A ∧
      (∀ (m : ℕ) (u a₀ : BitString), a₀ ∈ A (m, u) → a₀.length ≤ m ∧ u ∈ D (a₀, [])) ∧
      ∀ (m : ℕ) (u : BitString), (∃ a₀ : BitString, a₀.length ≤ m ∧ u ∈ D (a₀, [])) →
        (A (m, u)).Dom := by
  let G : ℕ × BitString → BitString →. BitString := fun z a₀ =>
    (D (a₀, [])).bind fun u' =>
      ((if u' = z.2 ∧ a₀.length ≤ z.1 then some a₀ else none : Option BitString) : Part BitString)
  have hG : Partrec (fun z : (ℕ × BitString) × BitString => G z.1 z.2) := by
    have h1 : Partrec (fun z : (ℕ × BitString) × BitString => D (z.2, [])) :=
      hD.comp (Computable.pair Computable.snd (Computable.const [])).partrec
    have h2 : Computable₂ (fun (z : (ℕ × BitString) × BitString) (u' : BitString) =>
        (if u' = z.1.2 ∧ z.2.length ≤ z.1.1 then some z.2 else none : Option BitString)) := by
      have hc : PrimrecPred (fun q : ((ℕ × BitString) × BitString) × BitString =>
          q.2 = q.1.1.2 ∧ q.1.2.length ≤ q.1.1.1) := by
        refine PrimrecPred.and (Primrec.eq.comp Primrec.snd
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) ?_
        exact Primrec.nat_le.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      exact (Primrec.ite hc (Primrec.option_some.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.const none)).to_comp
    exact Partrec.bind h1 (Computable.ofOption h2)
  obtain ⟨H, hH, hHs, hHd⟩ :=
    problemK_peirce_singleton_le_log_complexity_programs_search G hG
  refine ⟨H, hH, ?_, ?_⟩
  · intro m u a₀ ha
    obtain ⟨b, hb⟩ := hHs _ _ ha
    simp only [G, Part.mem_bind_iff] at hb
    obtain ⟨u', hu', hb⟩ := hb
    by_cases hcond : u' = u ∧ b.length ≤ m
    · simp only [hcond, and_self, ite_true] at hb
      have : a₀ = b := by simpa using hb
      subst this
      obtain ⟨rfl, hl⟩ := hcond
      exact ⟨hl, hu'⟩
    · simp [hcond] at hb
  · rintro m u ⟨a₀, hl, hu⟩
    refine hHd (m, u) a₀ ?_
    simp only [G]
    rw [Part.dom_iff_mem]
    exact ⟨a₀, Part.mem_bind_iff.2 ⟨u, hu, by simp [hl]⟩⟩

/-- Step 1 of the proof of `problemK_peirce_singleton_le_log_complexity`: the programs
`l_τ` (Gödel property of `P.lang`).  There is a total computable `ℓ (m, c, d, a, b)` such that
for every `m` and every string `u` having a program of length at most `m` (with `D`), the
program `ℓ m c d a b` run on `u` first finds one such program `a₀` (the same `a₀` for all
`c d a b`: a dovetailed search in `D`, which depends on `m` and `u` only) and then outputs
`D (τ a₀)`, where `τ` is the two-point map
`problemK_peirce_singleton_le_log_complexity_tau c d a b` (`τ(c) = d`, else `τ(a) = b`, else `[]`).
-/
private theorem problemK_peirce_singleton_le_log_complexity_programs (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ ℓ : ℕ → BitString → BitString → BitString → BitString → BitString,
      Computable (fun r : ℕ × BitString × BitString × BitString × BitString =>
        ℓ r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2) ∧
      ∀ (m : ℕ) (u : BitString), (∃ a₀ : BitString, a₀.length ≤ m ∧ u ∈ D (a₀, [])) →
        ∃ a₀ : BitString, a₀.length ≤ m ∧ u ∈ D (a₀, []) ∧
          ∀ c d a b : BitString, P.lang (ℓ m c d a b, u) =
            D (problemK_peirce_singleton_le_log_complexity_tau c d a b a₀, []) := by
  obtain ⟨-, -, -, -, -, hL, hG⟩ := hP
  obtain ⟨A, hA, hAs, hAd⟩ :=
    problemK_peirce_singleton_le_log_complexity_programs_find D hD.1
  let dec : ℕ → ℕ × BitString × BitString × BitString × BitString := fun n =>
    (Encodable.decode (α := ℕ × BitString × BitString × BitString × BitString) n).getD
      (0, [], [], [], [])
  have hdec : Computable dec :=
    Computable.option_getD Computable.decode (Computable.const _)
  let V : Map := fun r =>
    (A ((dec r.1.length).1, r.2)).bind fun a₀ =>
      D (problemK_peirce_singleton_le_log_complexity_tau (dec r.1.length).2.1
        (dec r.1.length).2.2.1 (dec r.1.length).2.2.2.1 (dec r.1.length).2.2.2.2 a₀, [])
  have hV : Partrec V := by
    have hs : Computable (fun r : BitString × BitString => dec r.1.length) :=
      hdec.comp (Computable.list_length.comp Computable.fst)
    have h1 : Partrec (fun r : BitString × BitString => A ((dec r.1.length).1, r.2)) :=
      hA.comp ((Computable.fst.comp hs).pair Computable.snd)
    have h2 : Computable₂ (fun (r : BitString × BitString) (a₀ : BitString) =>
        (problemK_peirce_singleton_le_log_complexity_tau (dec r.1.length).2.1
          (dec r.1.length).2.2.1 (dec r.1.length).2.2.2.1 (dec r.1.length).2.2.2.2 a₀,
            ([] : BitString))) := by
      have hτ := problemK_peirce_singleton_le_log_complexity_programs_tau_primrec
      have hs' : Computable (fun q : (BitString × BitString) × BitString =>
          dec q.1.1.length) := hs.comp Computable.fst
      have hc : Computable (fun q : (BitString × BitString) × BitString =>
          (dec q.1.1.length).2.1) := Computable.fst.comp (Computable.snd.comp hs')
      have hd : Computable (fun q : (BitString × BitString) × BitString =>
          (dec q.1.1.length).2.2.1) :=
        Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hs'))
      have ha : Computable (fun q : (BitString × BitString) × BitString =>
          (dec q.1.1.length).2.2.2.1) :=
        Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hs')))
      have hb : Computable (fun q : (BitString × BitString) × BitString =>
          (dec q.1.1.length).2.2.2.2) :=
        Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hs')))
      refine Computable.pair ?_ (Computable.const [])
      have key := Computable.comp hτ.to_comp
        (hc.pair (hd.pair (ha.pair (hb.pair (Computable.snd :
          Computable (fun q : (BitString × BitString) × BitString => q.2))))))
      exact key
    exact Partrec.bind h1 (hD.1.comp h2.partrec)
  obtain ⟨t, ht, hts⟩ := hG V hV
  refine ⟨fun m c d a b => t (List.replicate (Encodable.encode (m, c, d, a, b)) false), ?_, ?_⟩
  · refine ht.comp ?_
    exact (Primrec.list_replicate.comp
      (Primrec.encode.comp Primrec.id) (Primrec.const false)).to_comp
  · intro m u hu
    obtain ⟨a₀, ha₀⟩ := Part.dom_iff_mem.1 (hAd m u hu)
    obtain ⟨hl, hD0⟩ := hAs m u a₀ ha₀
    refine ⟨a₀, hl, hD0, fun c d a b => ?_⟩
    rw [hts]
    simp only [V, List.length_replicate, Encodable.encodek, Option.getD_some, dec]
    rw [Part.eq_some_iff.2 ha₀, Part.bind_some]

/-- Generic search: an enumerable relation (given by a computable stage test) has a partial
computable selector, defined wherever a witness exists and with every output a witness. -/
private theorem problemK_peirce_singleton_le_log_complexity_search_select
    {α β : Type} [Primcodable α] [Primcodable β] (R : α → β → Prop)
    (chk : α × β → ℕ → Bool) (hchk : Computable₂ chk)
    (hiff : ∀ a b, R a b ↔ ∃ s, chk (a, b) s = true) :
    ∃ F : α →. β, Partrec F ∧ (∀ a b, b ∈ F a → R a b) ∧ (∀ a b, R a b → (F a).Dom) := by
  let g : α → ℕ → Option β := fun a m =>
    (Encodable.decode (α := β) m.unpair.1).bind
      (fun b => bif chk (a, b) m.unpair.2 then some b else none)
  have hg : Computable₂ g := by
    have h1 : Computable (fun z : α × ℕ => Encodable.decode (α := β) z.2.unpair.1) :=
      Computable.decode.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
    have h2 : Computable₂ (fun (z : α × ℕ) (b : β) =>
        bif chk (z.1, b) z.2.unpair.2 then some b else none) := by
      refine Computable.cond (hchk.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)
        (Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst))))
        (Computable.option_some.comp Computable.snd) (Computable.const none)
    exact (Computable.option_bind h1 h2).to₂
  refine ⟨fun a => Nat.rfindOpt (g a), Partrec.rfindOpt hg, ?_, ?_⟩
  · intro a b hb
    obtain ⟨m, hm⟩ := Nat.rfindOpt_spec hb
    simp only [g, Option.mem_def, Option.bind_eq_some_iff] at hm
    obtain ⟨b', hb', hc⟩ := hm
    cases hck : chk (a, b') m.unpair.2
    · simp [hck] at hc
    · simp only [hck, Bool.cond_true, Option.some.injEq] at hc
      subst hc
      exact (hiff a b').2 ⟨_, hck⟩
  · intro a b hab
    obtain ⟨s, hs⟩ := (hiff a b).1 hab
    refine Nat.rfindOpt_dom.2 ⟨Nat.pair (Encodable.encode b) s, b, ?_⟩
    simp [g, hs]

/-- A finite list of monotone stage conditions holds at a common stage. -/
private theorem problemK_peirce_singleton_le_log_complexity_search_stage {β : Type*}
    (Q : β → ℕ → Prop) (hmono : ∀ x s t, s ≤ t → Q x s → Q x t) :
    ∀ l : List β, (∀ x ∈ l, ∃ s, Q x s) → ∃ s, ∀ x ∈ l, Q x s := by
  intro l
  induction l with
  | nil => intro _; exact ⟨0, by simp⟩
  | cons x t ih =>
    intro h
    obtain ⟨s1, hs1⟩ := h x (by simp)
    obtain ⟨s2, hs2⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    refine ⟨max s1 s2, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hmono _ _ _ (le_max_left _ _) hs1
    · exact hmono _ _ _ (le_max_right _ _) (hs2 y hy)

/-- Step 2 of the proof of `problemK_peirce_singleton_le_log_complexity`: the search for
a compatible pair.  For a computable family `ℓ` of programs there is a partial computable
`F (m, p)` (dovetail over all pairs `(a, b)` of strings of length at most `m`, over the finitely
many `(c, d)`, and over the running times of `P.lang` and `D`; output `D(a)` for the first
pair found compatible) which is defined whenever some pair is compatible with `p`, and whose
every value is `D(a)` for some pair `(a, b)` compatible with `p`. -/
private theorem problemK_peirce_singleton_le_log_complexity_search (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible)
    (ℓ : ℕ → BitString → BitString → BitString → BitString → BitString)
    (hℓ : Computable (fun r : ℕ × BitString × BitString × BitString × BitString =>
        ℓ r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2)) :
    ∃ F : ℕ × BitString →. BitString, Partrec F ∧ ∀ (m : ℕ) (p : BitString),
      ((∃ a b : BitString, problemK_peirce_singleton_le_log_complexity_compat D P ℓ m p a b) →
        ∃ v, v ∈ F (m, p)) ∧
      ∀ v ∈ F (m, p), ∃ a b : BitString,
        problemK_peirce_singleton_le_log_complexity_compat D P ℓ m p a b ∧ v ∈ D (a, []) := by
  classical
  have hDp : Partrec D := hD.1
  have hLp : Partrec P.lang := hP.2.2.2.2.2.1
  -- the atomic condition: both computations halt with the same value
  let W : (ℕ × BitString × BitString × BitString × BitString × BitString) →. Unit := fun r =>
    (P.lang (r.2.1, ℓ r.1 r.2.2.2.2.1 r.2.2.2.2.2 r.2.2.1 r.2.2.2.1)).bind fun v =>
      (D (r.2.2.1, [])).bind fun v' =>
        (↑(bif decide (v = v') then some () else none : Option Unit) : Part Unit)
  have hW : Partrec W := by
    have pm : Computable (fun r : ℕ × BitString × BitString × BitString × BitString × BitString =>
        r.1) := Computable.fst
    have pp : Computable (fun r : ℕ × BitString × BitString × BitString × BitString × BitString =>
        r.2.1) := Computable.fst.comp Computable.snd
    have pa : Computable (fun r : ℕ × BitString × BitString × BitString × BitString × BitString =>
        r.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
    have pb : Computable (fun r : ℕ × BitString × BitString × BitString × BitString × BitString =>
        r.2.2.2.1) :=
      Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
    have pc : Computable (fun r : ℕ × BitString × BitString × BitString × BitString × BitString =>
        r.2.2.2.2.1) :=
      Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
        Computable.snd)))
    have pd : Computable (fun r : ℕ × BitString × BitString × BitString × BitString × BitString =>
        r.2.2.2.2.2) :=
      Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
        Computable.snd)))
    have hr1 : Computable (fun r : ℕ × BitString × BitString × BitString × BitString × BitString =>
        (r.2.1, ℓ r.1 r.2.2.2.2.1 r.2.2.2.2.2 r.2.2.1 r.2.2.2.1)) :=
      pp.pair (hℓ.comp (pm.pair (pc.pair (pd.pair (pa.pair pb)))))
    have hr2 : Computable (fun r : (ℕ × BitString × BitString × BitString × BitString × BitString)
        × BitString => (r.1.2.2.1, ([] : BitString))) :=
      (pa.comp Computable.fst).pair (Computable.const [])
    refine (hLp.comp hr1).bind ?_
    refine Partrec.bind (hDp.comp hr2) ?_
    refine Computable.ofOption ?_
    refine Computable.cond ?_ (Computable.const (some ())) (Computable.const none)
    exact (primrec_decideEq.to_comp).comp (Computable.snd.comp Computable.fst) Computable.snd
  have hWdom : ∀ r : ℕ × BitString × BitString × BitString × BitString × BitString,
      (W r).Dom ↔ ∃ v, v ∈ P.lang (r.2.1, ℓ r.1 r.2.2.2.2.1 r.2.2.2.2.2 r.2.2.1 r.2.2.2.1) ∧
        v ∈ D (r.2.2.1, []) := by
    intro r
    rw [Part.dom_iff_mem]
    constructor
    · rintro ⟨u, hu⟩
      simp only [W, Part.mem_bind_iff] at hu
      obtain ⟨v, hv, v', hv', hu⟩ := hu
      by_cases h : v = v'
      · subst h; exact ⟨v, hv, hv'⟩
      · simp [h] at hu
    · rintro ⟨v, hv, hv'⟩
      refine ⟨(), ?_⟩
      simp only [W, Part.mem_bind_iff]
      exact ⟨v, hv, v, hv', by simp⟩
  obtain ⟨chkT, hchkT, hmonoT, hiffT⟩ := IsRE.exists_stageApprox
    (R := fun r : ℕ × BitString × BitString × BitString × BitString × BitString =>
      ∃ v, v ∈ P.lang (r.2.1, ℓ r.1 r.2.2.2.2.1 r.2.2.2.2.2 r.2.2.1 r.2.2.2.1) ∧
        v ∈ D (r.2.2.1, [])) ⟨W, hW, hWdom⟩
  -- the stage test for compatibility
  let badf : (((ℕ × BitString) × (BitString × BitString)) × ℕ) × BitString × BitString → Bool :=
    fun y => (!decide (y.2.1 = y.1.1.2.1) || decide (y.2.2 = y.1.1.2.2)) &&
      !chkT (y.1.1.1.1, y.1.1.1.2, y.1.1.2.1, y.1.1.2.2, y.2.1, y.2.2) y.1.2
  have hbad : Computable badf := by
    have q1 : Computable (fun y : (((ℕ × BitString) × (BitString × BitString)) × ℕ) ×
        BitString × BitString => y.2.1) := Computable.fst.comp Computable.snd
    have q2 : Computable (fun y : (((ℕ × BitString) × (BitString × BitString)) × ℕ) ×
        BitString × BitString => y.2.2) := Computable.snd.comp Computable.snd
    have qa : Computable (fun y : (((ℕ × BitString) × (BitString × BitString)) × ℕ) ×
        BitString × BitString => y.1.1.2.1) :=
      Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
    have qb : Computable (fun y : (((ℕ × BitString) × (BitString × BitString)) × ℕ) ×
        BitString × BitString => y.1.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
    have qm : Computable (fun y : (((ℕ × BitString) × (BitString × BitString)) × ℕ) ×
        BitString × BitString => y.1.1.1.1) :=
      Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
    have qp : Computable (fun y : (((ℕ × BitString) × (BitString × BitString)) × ℕ) ×
        BitString × BitString => y.1.1.1.2) :=
      Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
    have qs : Computable (fun y : (((ℕ × BitString) × (BitString × BitString)) × ℕ) ×
        BitString × BitString => y.1.2) := Computable.snd.comp Computable.fst
    have hT : Computable (fun y : (((ℕ × BitString) × (BitString × BitString)) × ℕ) ×
        BitString × BitString =>
        chkT (y.1.1.1.1, y.1.1.1.2, y.1.1.2.1, y.1.1.2.2, y.2.1, y.2.2) y.1.2) :=
      hchkT.comp (qm.pair (qp.pair (qa.pair (qb.pair (q1.pair q2))))) qs
    have h1 : Computable (fun y : (((ℕ × BitString) × (BitString × BitString)) × ℕ) ×
        BitString × BitString => decide (y.2.1 = y.1.1.2.1)) :=
      primrec_decideEq.to_comp.comp q1 qa
    have h2 : Computable (fun y : (((ℕ × BitString) × (BitString × BitString)) × ℕ) ×
        BitString × BitString => decide (y.2.2 = y.1.1.2.2)) :=
      primrec_decideEq.to_comp.comp q2 qb
    exact Primrec.and.to_comp.comp
      (Primrec.or.to_comp.comp (Primrec.not.to_comp.comp h1) h2)
      (Primrec.not.to_comp.comp hT)
  let chk : ((ℕ × BitString) × (BitString × BitString)) → ℕ → Bool := fun z s =>
    decide (z.2.1.length ≤ z.1.1) && decide (z.2.2.length ≤ z.1.1) &&
      !((allStringsUpTo z.1.1).any fun c => (allStringsUpTo z.1.1).any fun d => badf ((z, s), c, d))
  have hchk : Computable₂ chk := by
    have hL : Computable (fun x : ((ℕ × BitString) × (BitString × BitString)) × ℕ =>
        allStringsUpTo x.1.1.1) :=
      allStringsUpTo_primrec.to_comp.comp
        (Computable.fst.comp (Computable.fst.comp Computable.fst))
    have hL2 : Computable (fun x : (((ℕ × BitString) × (BitString × BitString)) × ℕ) × BitString =>
        allStringsUpTo x.1.1.1.1) :=
      allStringsUpTo_primrec.to_comp.comp
        (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
    have hinner : Computable₂ (fun (x : ((ℕ × BitString) × (BitString × BitString)) × ℕ)
        (c : BitString) => (allStringsUpTo x.1.1.1).any fun d => badf (x, c, d)) := by
      refine computable_list_any (f := fun x : (((ℕ × BitString) × (BitString × BitString)) × ℕ) ×
        BitString => allStringsUpTo x.1.1.1.1) (p := fun x d => badf (x.1, x.2, d)) hL2 ?_
      refine hbad.comp ?_
      exact ((Computable.fst.comp Computable.fst).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd))
    have hany : Computable (fun x : ((ℕ × BitString) × (BitString × BitString)) × ℕ =>
        (allStringsUpTo x.1.1.1).any fun c => (allStringsUpTo x.1.1.1).any fun d =>
          badf (x, c, d)) :=
      computable_list_any (f := fun x : ((ℕ × BitString) × (BitString × BitString)) × ℕ =>
        allStringsUpTo x.1.1.1) (p := fun x c => (allStringsUpTo x.1.1.1).any fun d =>
          badf (x, c, d)) hL hinner
    have e1 : Computable (fun x : ((ℕ × BitString) × (BitString × BitString)) × ℕ =>
        decide (x.1.2.1.length ≤ x.1.1.1)) :=
      (Primrec.nat_le.decide.to_comp).comp
        (Primrec.list_length.to_comp.comp (Computable.fst.comp (Computable.snd.comp
          Computable.fst)))
        (Computable.fst.comp (Computable.fst.comp Computable.fst))
    have e2 : Computable (fun x : ((ℕ × BitString) × (BitString × BitString)) × ℕ =>
        decide (x.1.2.2.length ≤ x.1.1.1)) :=
      (Primrec.nat_le.decide.to_comp).comp
        (Primrec.list_length.to_comp.comp (Computable.snd.comp (Computable.snd.comp
          Computable.fst)))
        (Computable.fst.comp (Computable.fst.comp Computable.fst))
    exact Primrec.and.to_comp.comp (Primrec.and.to_comp.comp e1 e2)
      (Primrec.not.to_comp.comp hany)
  have hspec : ∀ (z : (ℕ × BitString) × (BitString × BitString)) (s : ℕ),
      chk z s = true ↔ z.2.1.length ≤ z.1.1 ∧ z.2.2.length ≤ z.1.1 ∧
        ∀ c d : BitString, c.length ≤ z.1.1 → d.length ≤ z.1.1 → (c = z.2.1 → d = z.2.2) →
          chkT (z.1.1, z.1.2, z.2.1, z.2.2, c, d) s = true := by
    intro z s
    simp only [chk, badf, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      List.any_eq_false, mem_allStringsUpTo,
      Bool.not_eq_true, Bool.or_eq_true, decide_eq_false_iff_not,
      and_assoc]
    refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
    constructor
    · intro h c d hc hd hcd
      by_contra hne
      have hf : chkT (z.1.1, z.1.2, z.2.1, z.2.2, c, d) s = false := by simpa using hne
      refine h c hc d hd ⟨?_, hf⟩
      by_cases hca : c = z.2.1
      · exact Or.inr (hcd hca)
      · exact Or.inl hca
    · rintro h c hc d hd ⟨h1, h2⟩
      have := h c d hc hd (fun hca => h1.resolve_left (not_not.2 hca))
      rw [this] at h2
      exact Bool.noConfusion h2
  have hiff : ∀ (mp : ℕ × BitString) (ab : BitString × BitString),
      problemK_peirce_singleton_le_log_complexity_compat D P ℓ mp.1 mp.2 ab.1 ab.2 ↔
        ∃ s, chk (mp, ab) s = true := by
    intro mp ab
    obtain ⟨m, p⟩ := mp
    obtain ⟨a, b⟩ := ab
    simp only [hspec]
    constructor
    · rintro ⟨ha, hb, h⟩
      obtain ⟨s, hs⟩ := problemK_peirce_singleton_le_log_complexity_search_stage
        (fun cd s => (cd.1 = a → cd.2 = b) → chkT (m, p, a, b, cd.1, cd.2) s = true)
        (by intro cd s t hst hs h'; exact hmonoT _ _ _ hst (hs h'))
        ((allStringsUpTo m).flatMap fun c => (allStringsUpTo m).map fun d => (c, d))
        (by
          intro cd hcd
          simp only [List.mem_flatMap, List.mem_map, mem_allStringsUpTo] at hcd
          obtain ⟨c, hc, d, hd, rfl⟩ := hcd
          by_cases hh : c = a → d = b
          · obtain ⟨v, hv1, hv2⟩ := h c d hc hd hh
            obtain ⟨s, hs⟩ := (hiffT (m, p, a, b, c, d)).1 ⟨v, hv1, hv2⟩
            exact ⟨s, fun _ => hs⟩
          · exact ⟨0, fun h' => absurd h' hh⟩)
      refine ⟨s, ha, hb, fun c d hc hd hcd => ?_⟩
      exact hs (c, d) (by
        simp only [List.mem_flatMap, List.mem_map, mem_allStringsUpTo]
        exact ⟨c, hc, d, hd, rfl⟩) hcd
    · rintro ⟨s, ha, hb, h⟩
      refine ⟨ha, hb, fun c d hc hd hcd => ?_⟩
      exact (hiffT (m, p, a, b, c, d)).2 ⟨s, h c d hc hd hcd⟩
  obtain ⟨Fs, hFs, hsound, hcomp⟩ :=
    problemK_peirce_singleton_le_log_complexity_search_select
      (fun mp ab => problemK_peirce_singleton_le_log_complexity_compat D P ℓ mp.1 mp.2 ab.1 ab.2)
      chk hchk hiff
  refine ⟨fun mp => (Fs mp).bind fun ab => D (ab.1, []), ?_, ?_⟩
  · refine hFs.bind ?_
    exact hDp.comp ((Computable.fst.comp Computable.snd).pair (Computable.const []))
  · intro m p
    constructor
    · rintro ⟨a, b, hab⟩
      obtain ⟨c0, hc0⟩ := Part.dom_iff_mem.1 (hcomp (m, p) (a, b) hab)
      obtain ⟨hl1, hl2, hall⟩ := hsound (m, p) c0 hc0
      obtain ⟨v, -, hv⟩ := hall c0.1 c0.2 hl1 hl2 (fun _ => rfl)
      exact ⟨v, Part.mem_bind_iff.2 ⟨c0, hc0, hv⟩⟩
    · intro v hv
      obtain ⟨ab, hab, hvD⟩ := Part.mem_bind_iff.1 hv
      exact ⟨ab.1, ab.2, hsound (m, p) ab hab, hvD⟩

/-- Step 3 of the proof of `problemK_peirce_singleton_le_log_complexity`: the logical
core (two programs of length at most `m` for `x`, `y`; `ℓ` as in step 1).  For every solution
`p` of `(x → y) → x` there is a compatible pair, and every compatible pair `(a, b)` has
`x ∈ D(a)`. -/
private theorem problemK_peirce_singleton_le_log_complexity_logic (D : Map)
    (P : ProblemCalculus)
    (ℓ : ℕ → BitString → BitString → BitString → BitString → BitString)
    (hℓ : ∀ (m : ℕ) (u : BitString), (∃ a₀ : BitString, a₀.length ≤ m ∧ u ∈ D (a₀, [])) →
        ∃ a₀ : BitString, a₀.length ≤ m ∧ u ∈ D (a₀, []) ∧
          ∀ c d a b : BitString, P.lang (ℓ m c d a b, u) =
            D (problemK_peirce_singleton_le_log_complexity_tau c d a b a₀, []))
    (x y : BitString) (m : ℕ)
    (hx : ∃ a : BitString, a.length ≤ m ∧ x ∈ D (a, []))
    (hy : ∃ a : BitString, a.length ≤ m ∧ y ∈ D (a, []))
    (p : BitString) (hp : p ∈ P.imp (P.imp {x} {y}) {x}) :
    (∃ a b : BitString, problemK_peirce_singleton_le_log_complexity_compat D P ℓ m p a b) ∧
      ∀ a b : BitString,
        problemK_peirce_singleton_le_log_complexity_compat D P ℓ m p a b → x ∈ D (a, []) := by
  classical
  obtain ⟨x', hx'len, hx'D, hx'τ⟩ := hℓ m x hx
  obtain ⟨y', hy'len, hy'D⟩ := hy
  have key : ∀ c d a b : BitString,
      problemK_peirce_singleton_le_log_complexity_tau c d a b x' = y' →
        ℓ m c d a b ∈ P.imp {x} {y} := by
    intro c d a b h u hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    refine ⟨y, rfl, ?_⟩
    rw [hx'τ c d a b, h]
    exact hy'D
  have sol : ∀ c d a b : BitString,
      problemK_peirce_singleton_le_log_complexity_tau c d a b x' = y' →
        ∀ v, v ∈ P.lang (p, ℓ m c d a b) → v = x := by
    intro c d a b h v hv
    obtain ⟨w, hw, hwv⟩ := hp _ (key c d a b h)
    rw [Set.mem_singleton_iff] at hw
    rw [hw] at hwv
    exact Part.mem_unique hv hwv
  refine ⟨⟨x', y', hx'len, hy'len, fun c d hc hd hcd => ?_⟩, ?_⟩
  · have hτ : problemK_peirce_singleton_le_log_complexity_tau c d x' y' x' = y' := by
      unfold problemK_peirce_singleton_le_log_complexity_tau
      by_cases h : x' = c
      · simp [h, hcd h.symm]
      · simp [h]
    obtain ⟨w, hw, hwv⟩ := hp _ (key c d x' y' hτ)
    rw [Set.mem_singleton_iff] at hw
    exact ⟨w, hwv, by rw [hw]; exact hx'D⟩
  · rintro a b ⟨ha, hb, h⟩
    by_cases hax : a = x'
    · rw [hax]; exact hx'D
    · obtain ⟨v, hv, hvD⟩ := h x' y' hx'len hy'len (fun h' => absurd h'.symm hax)
      have hτ : problemK_peirce_singleton_le_log_complexity_tau x' y' a b x' = y' := by
        simp [problemK_peirce_singleton_le_log_complexity_tau]
      rw [← sol x' y' a b hτ v hv]
      exact hvD

/-- Step 4 of the proof of `problemK_peirce_singleton_le_log_complexity`: the Gödel
property applied to a partial computable `F (m, p)`: the program `g m` computing `F m` is
obtained from `m` by a computable map, `[g m](p) = F (m, p)`. -/
private theorem problemK_peirce_singleton_le_log_complexity_goedel (P : ProblemCalculus)
    (hP : P.Admissible) (F : ℕ × BitString →. BitString) (hF : Partrec F) :
    ∃ g : ℕ → BitString, Computable g ∧ ∀ (m : ℕ) (p : BitString), P.lang (g m, p) = F (m, p) := by
  obtain ⟨-, -, -, -, -, -, hG⟩ := hP
  obtain ⟨t, ht, hts⟩ := hG (fun q => F (q.1.length, q.2))
    (hF.comp (Computable.pair (Primrec.list_length.to_comp.comp Computable.fst) Computable.snd))
  have hrep : Computable (fun m : ℕ => (List.replicate m false : BitString)) := by
    have : Primrec (fun m : ℕ => (List.range m).map (fun _ => false)) :=
      Primrec.list_map Primrec.list_range (Primrec.const false).to₂
    refine this.to_comp.of_eq fun m => ?_
    simp [List.map_const', List.length_range]
  refine ⟨fun m => t (List.replicate m false), ht.comp hrep, fun m p => ?_⟩
  rw [hts]
  simp

/-- SUV Problem 341 (Section 13.3, printed p. 406).  In Theorem 239 `O(log n)` can be replaced
by `O(log m)`, `m = max (C(x), C(y))` (a constant when `m = 0`; `C` is finite for an optimal
`D`, so `toNat` loses nothing).  Hint (book): work with shortest programs of `x` and `y`
instead of `x`, `y`; `S` becomes the strings of length at most `m`, and `l_τ` on input `u`
searches for the first program of length at most `m` producing `u` (with `D`), applies `τ` and
decompresses the result.  With `x'` the first program found for `x` and `y'` a shortest program
for `y`, every `l_τ` with `τ(x') = y'` solves `x → y`; call `(a, b) ∈ S × S` compatible with `p`
if `[p](l_τ) = D(a)` for all `τ` with `τ(a) = b`.  `(x', y')` is compatible and every compatible
`(a, b)` has `D(a) = x`, so `x` is computed from `p` and `m`. -/
theorem problemK_peirce_singleton_le_log_complexity (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ x y : BitString,
      problemK D (P.imp (P.imp (P.imp {x} {y}) {x}) {x}) ≤
        (logSlack k (max (plainK D x).toNat (plainK D y).toNat) : ℕ∞) := by
  obtain ⟨ℓ, hℓc, hℓ⟩ := problemK_peirce_singleton_le_log_complexity_programs D hD P hP
  obtain ⟨F, hF, hFspec⟩ :=
    problemK_peirce_singleton_le_log_complexity_search D hD P hP ℓ hℓc
  obtain ⟨g, hg, hgF⟩ := problemK_peirce_singleton_le_log_complexity_goedel P hP F hF
  obtain ⟨c, hc⟩ := problemK_le_of_partrec_advice D hD
    (fun r : BitString × (ℕ × Bool) => Part.some (g r.2.1))
    (hg.comp (Computable.fst.comp Computable.snd))
  obtain ⟨cl, hcl⟩ := plainK_le_length D hD
  refine ⟨c + cl, fun x y => ?_⟩
  set m := max (plainK D x).toNat (plainK D y).toNat with hm
  -- a string of complexity at most `m` has a program of length at most `m`
  have hprog : ∀ z : BitString, (plainK D z).toNat ≤ m → ∃ a : BitString,
      a.length ≤ m ∧ z ∈ D (a, []) := by
    intro z hz
    have hfin : plainK D z ≠ ⊤ := ne_top_of_le_natCast_add (hcl z)
    have hlt : plainK D z < ((m + 1 : ℕ) : ℕ∞) := by
      rw [← ENat.natCast_toNat hfin]
      exact_mod_cast Nat.lt_succ_of_le hz
    rw [plainK, condK, sInf_lt_iff] at hlt
    obtain ⟨n, ⟨p, hp, rfl⟩, hlt⟩ := hlt
    exact ⟨p, by exact_mod_cast Nat.le_of_lt_succ (by exact_mod_cast hlt), hp⟩
  have hx := hprog x (le_max_left _ _)
  have hy := hprog y (le_max_right _ _)
  have hmem : g m ∈ P.imp (P.imp (P.imp {x} {y}) {x}) {x} := by
    intro p hp
    obtain ⟨⟨a, b, hab⟩, hall⟩ :=
      problemK_peirce_singleton_le_log_complexity_logic D P ℓ
        (fun m u hu => hℓ m u hu) x y m hx hy p hp
    obtain ⟨v, hv⟩ := (hFspec m p).1 ⟨a, b, hab⟩
    obtain ⟨a', b', hab', hva⟩ := (hFspec m p).2 v hv
    have hvx : v = x := Part.mem_unique hva (hall a' b' hab')
    subst hvx
    exact ⟨v, rfl, by rw [hgF]; exact hv⟩
  have hmain := hc {[]} (P.imp (P.imp (P.imp {x} {y}) {x}) {x}) m
    (fun _ _ => ⟨false, g m, hmem, Part.mem_some _⟩)
  calc problemK D (P.imp (P.imp (P.imp {x} {y}) {x}) {x})
      ≤ problemK D {[]} + (logSlack c m : ℕ∞) := hmain
    _ ≤ (cl : ℕ∞) + (logSlack c m : ℕ∞) := by
        rw [problemK_singleton]
        gcongr
        simpa using hcl []
    _ ≤ (logSlack (c + cl) m : ℕ∞) := by
        have h1 : cl ≤ logSlack cl m := by unfold logSlack; exact Nat.le_add_left _ _
        have : cl + logSlack c m ≤ logSlack (c + cl) m := by
          rw [logSlack_add_constants]; omega
        exact_mod_cast this

/-- The trivial inequality `C((x → y) → x) ≤ C(x) + O(1)` (copy of
`problemK_imp_imp_singleton_le_plainK`, which is stated after the target). -/
private theorem plainK_le_problemK_imp_imp_singleton_aux_upper (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ x y : BitString,
      problemK D (P.imp (P.imp {x} {y}) {x}) ≤ plainK D x + (k : ℕ∞) := by
  obtain ⟨-, -, -, -, -, -, hG⟩ := hP
  obtain ⟨t, ht, hts⟩ := hG (fun pr => Part.some pr.1) Computable.fst.partrec
  obtain ⟨c, hc⟩ := plainK_map_le D hD t ht
  refine ⟨c, fun x y => ?_⟩
  have hmem : t x ∈ P.imp (P.imp {x} {y}) {x} := by
    intro w _
    exact ⟨x, Set.mem_singleton x, by rw [hts]; exact Part.mem_some x⟩
  exact (problemK_le_of_mem D hmem).trans (hc x)

/-- SUV Section 13.3, corollary of Theorem 239 (printed p. 406).
`C(x) ≤ C((x → y) → x) + O(log n)` for all strings `x`, `y` of length at most `n`.  Book's
proof: Theorem 239 together with the inequality `C(Y) ≤ C(X) + C(X → Y) + O(log C(X))`
(`problemK_le_add_imp`) for `X = (x → y) → x` and `Y = {x}`: `C(X → {x}) = O(log n)` by Theorem
239 (`problemK_peirce_singleton_le_log`), and `C(X) ≤ C(x) + O(1) ≤ n + O(1)`
(`problemK_imp_imp_singleton_le_plainK`, `plainK_le_length`), so `O(log C(X)) = O(log n)`
(`logSlack_mono_right`, `logSlack_add_le`). -/
theorem plainK_le_problemK_imp_imp_singleton (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (x y : BitString), x.length ≤ n → y.length ≤ n →
      plainK D x ≤ problemK D (P.imp (P.imp {x} {y}) {x}) + (logSlack k n : ℕ∞) := by
  obtain ⟨k1, hk1⟩ := problemK_peirce_singleton_le_log D hD P hP
  obtain ⟨c, hc⟩ := problemK_le_add_imp D hD P hP
  obtain ⟨c', hc'⟩ := plainK_le_problemK_imp_imp_singleton_aux_upper D hD P hP
  obtain ⟨cl, hcl⟩ := plainK_le_length D hD
  refine ⟨k1 + c + logSlack c (cl + c'), fun n x y hx hy => ?_⟩
  set X := P.imp (P.imp {x} {y}) {x} with hX
  set K := cl + c' with hK
  have hXle : problemK D X ≤ ((n + K : ℕ) : ℕ∞) := by
    calc problemK D X ≤ plainK D x + (c' : ℕ∞) := hc' x y
      _ ≤ ((programLength x : ℕ) : ℕ∞) + cl + c' := by gcongr; exact hcl x
      _ ≤ ((n + K : ℕ) : ℕ∞) := by
          have : programLength x ≤ n := hx
          rw [hK]; push_cast; rw [add_assoc]
          gcongr
  have hm : (problemK D X).toNat ≤ n + K := ENat.toNat_le_of_le_natCast hXle
  have hnat : logSlack k1 n + logSlack c (n + K) ≤ logSlack (k1 + c + logSlack c K) n := by
    have h1 : logSlack c (n + K) ≤ logSlack c n + logSlack c K := logSlack_add_le c n K
    have h2 : logSlack c K ≤ logSlack (logSlack c K) n := by
      generalize logSlack c K = j
      unfold logSlack; exact Nat.le_add_left _ _
    rw [logSlack_add_constants, logSlack_add_constants]
    omega
  have h3 := hc X {x}
  rw [problemK_singleton] at h3
  have h4 := hk1 n x y hx hy
  calc plainK D x ≤ problemK D X + problemK D (P.imp X {x}) +
        (logSlack c (problemK D X).toNat : ℕ∞) := h3
    _ ≤ problemK D X + (logSlack k1 n : ℕ∞) + (logSlack c (n + K) : ℕ∞) := by
        have h5 : problemK D (P.imp X {x}) ≤ (logSlack k1 n : ℕ∞) := h4
        have h6 : (logSlack c (problemK D X).toNat : ℕ∞) ≤ (logSlack c (n + K) : ℕ∞) := by
          exact_mod_cast logSlack_mono_right c hm
        gcongr
    _ = problemK D X + ((logSlack k1 n + logSlack c (n + K) : ℕ) : ℕ∞) := by
        push_cast; ring
    _ ≤ problemK D X + (logSlack (k1 + c + logSlack c K) n : ℕ∞) := by
        gcongr

/-- SUV Section 13.3, remark after Problem 341 (printed p. 406).  The reverse inequality
`C((x → y) → x) ≤ C(x) + O(1)` ("as the reverse inequality is trivial"); with
`plainK_le_problemK_imp_imp_singleton` it gives `C((x → y) → x) = C(x) + O(log n)`.  Proof: the
program that ignores its input and prints `x` solves the problem, and it is obtained from `x` by
a total computable map (Gödel property). -/
theorem problemK_imp_imp_singleton_le_plainK (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ x y : BitString,
      problemK D (P.imp (P.imp {x} {y}) {x}) ≤ plainK D x + (k : ℕ∞) := by
  obtain ⟨-, -, -, -, -, -, hG⟩ := hP
  obtain ⟨t, ht, hts⟩ := hG (fun pr => Part.some pr.1) Computable.fst.partrec
  obtain ⟨c, hc⟩ := plainK_map_le D hD t ht
  refine ⟨c, fun x y => ?_⟩
  have hmem : t x ∈ P.imp (P.imp {x} {y}) {x} := by
    intro w _
    exact ⟨x, Set.mem_singleton x, by rw [hts]; exact Part.mem_some x⟩
  exact (problemK_le_of_mem D hmem).trans (hc x)

/-- SUV Theorem 240 (Section 13.3, printed p. 406), first inequality.  The complexity of
`(x → y) → y` is at most that of `x ∨ y` up to `O(log n)` for strings of length at most `n`
(the proof gives `O(1)`).  Book's algorithm (1): `[1, y]` becomes the constant program `y`;
`[0, x]` becomes "apply the given solution of `x → y` to `x`" (`problemK_le_of_partrec`). -/
theorem problemK_imp_imp_singleton_le_disj (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (x y : BitString), x.length ≤ n → y.length ≤ n →
      problemK D (P.imp (P.imp {x} {y}) {y}) ≤
        problemK D (P.disj {x} {y}) + (logSlack k n : ℕ∞) := by
  obtain ⟨-, hunpair, hinv, -, -, hL, hG⟩ := hP
  have hsnd : Computable (fun z : BitString => ((P.unpair z).map Prod.snd).getD []) :=
    Computable.option_getD
      (Computable.option_map hunpair (Computable.snd.comp Computable.snd).to₂)
      (Computable.const [])
  -- `t0 [0, x]` applies its input to `x`; `t1 [1, y]` ignores its input and prints `y`
  obtain ⟨t0, ht0, hts0⟩ :=
    hG (fun q => P.lang (q.2, ((P.unpair q.1).map Prod.snd).getD []))
      (hL.comp (Computable.snd.pair (hsnd.comp Computable.fst)))
  obtain ⟨t1, ht1, hts1⟩ :=
    hG (fun q => Part.some (((P.unpair q.1).map Prod.snd).getD []))
      (hsnd.comp Computable.fst).partrec
  obtain ⟨c0, hc0⟩ := plainK_map_le D hD t0 ht0
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD t1 ht1
  refine ⟨max c0 c1, fun n x y _ _ => ?_⟩
  have hne : (P.disj {x} {y}).Nonempty :=
    ⟨P.pair P.tag0 x, Or.inl ⟨x, Set.mem_singleton x, rfl⟩⟩
  obtain ⟨z, hz, hzeq⟩ := exists_mem_plainK_eq_problemK D hne
  rw [← hzeq]
  rcases hz with ⟨x', hx', rfl⟩ | ⟨y', hy', rfl⟩
  · rw [Set.mem_singleton_iff] at hx'
    subst hx'
    have hmem : t0 (P.pair P.tag0 x') ∈ P.imp (P.imp {x'} {y}) {y} := by
      intro w hw
      obtain ⟨y'', hy'', hwy⟩ := hw x' (Set.mem_singleton x')
      refine ⟨y'', hy'', ?_⟩
      rw [hts0]
      simpa [hinv] using hwy
    calc _ ≤ plainK D (t0 (P.pair P.tag0 x')) := problemK_le_of_mem D hmem
      _ ≤ plainK D (P.pair P.tag0 x') + c0 := hc0 _
      _ ≤ plainK D (P.pair P.tag0 x') + (logSlack (max c0 c1) n : ℕ∞) := by
          gcongr
          exact (le_max_left c0 c1).trans (Nat.le_add_left _ _)
  · rw [Set.mem_singleton_iff] at hy'
    subst hy'
    have hmem : t1 (P.pair P.tag1 y') ∈ P.imp (P.imp {x} {y'}) {y'} := by
      intro w _
      refine ⟨y', Set.mem_singleton y', ?_⟩
      rw [hts1]
      simp [hinv]
    calc _ ≤ plainK D (t1 (P.pair P.tag1 y')) := problemK_le_of_mem D hmem
      _ ≤ plainK D (P.pair P.tag1 y') + c1 := hc1 _
      _ ≤ plainK D (P.pair P.tag1 y') + (logSlack (max c0 c1) n : ℕ∞) := by
          gcongr
          exact (le_max_right c0 c1).trans (Nat.le_add_left _ _)

end InformationLogic
end Kolmogorov
