import KolmogorovMathlib.MonotoneComplexity.GacsDayGame
import KolmogorovMathlib.Foundation.PrimrecExtras
import Mathlib.Data.List.FinRange

/-!
# Replaying a client strategy against a recorded server play

A strategy is a function of the whole history, but the constructions only ever need to run it
against a recorded list of server moves. `selfPlayAux` and `selfPlay` produce the client moves
obtained that way, and `replayStrategy` is the strategy that ignores the recorded client history
and replays its own moves (`replayStrategy_indep_client_history`). The identities
`selfPlayAux_ofFn`, `selfPlay_length` and `selfPlayAux_eq_rec` put the replay in the `Nat.rec`
shape that `Computable.nat_rec` accepts, yielding `computable₂_selfPlay` and
`computable₂_replayStrategy`: replaying a computable family of strategies is computable.
-/

namespace Kolmogorov

/-- The first `n` client moves a strategy produces when replayed against the recorded server
moves. -/
def selfPlayAux (σ : ClientStrategy) (ss : List ServerMove) : ℕ → List ClientMove
  | 0 => []
  | n + 1 =>
    let prev := selfPlayAux σ ss n
    prev ++ [σ (prev, ss.take n)]

/-- The client moves a strategy produces when replayed against a recorded list of server moves. -/
def selfPlay (σ : ClientStrategy) (ss : List ServerMove) : List ClientMove :=
  selfPlayAux σ ss ss.length

/-- The strategy that ignores the recorded client history and replays its own moves from the
server history. -/
def replayStrategy (σ : ClientStrategy) : ClientStrategy :=
  fun hist => σ (selfPlay σ hist.2, hist.2)

/-- Taking the first `n` entries of `List.ofFn f` restricts `f` to the first `n` indices. -/
lemma list_take_ofFn {α} {t : ℕ} (f : Fin t → α) (n : ℕ) (h : n ≤ t) :
    (List.ofFn f).take n = List.ofFn (fun i : Fin n => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩) := by
  apply List.ext_get
  · simp [h]
  · intro i hi1 hi2
    simp

/-- Replaying against the first `t` server moves reproduces the first `n` moves of the play. -/
lemma selfPlayAux_ofFn (σ : ClientStrategy) (sms : ℕ → ServerMove) (t n : ℕ) (h : n ≤ t) :
    selfPlayAux σ (List.ofFn fun i : Fin t => sms i) n =
    List.ofFn fun i : Fin n => playClient σ sms i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : n ≤ t := Nat.le_trans (Nat.le_succ n) h
    rw [selfPlayAux]
    rw [ih hn]
    rw [list_take_ofFn _ _ hn]
    have h1 : (List.ofFn fun i : Fin (n + 1) => playClient σ sms ↑i) =
      (List.ofFn fun i : Fin n => playClient σ sms ↑i) ++ [playClient σ sms n] := by
      exact List.ofFn_succ_last
    rw [h1]
    cases n with
    | zero =>
      rw [playClient]
      rfl
    | succ m =>
      rw [playClient]

/-- A replay produces one client move per recorded server move. -/
lemma selfPlay_length (σ : ClientStrategy) (ss : List ServerMove) :
    (selfPlay σ ss).length = ss.length := by
  have hAux : ∀ n, (selfPlayAux σ ss n).length = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [selfPlayAux, ih]
  exact hAux ss.length

/-- Replaying against the first `t` server moves reproduces the first `t` moves of the play. -/
lemma selfPlay_ofFn (σ : ClientStrategy) (sms : ℕ → ServerMove) (t : ℕ) :
    selfPlay σ (List.ofFn fun i : Fin t => sms i) =
    List.ofFn fun i : Fin t => playClient σ sms i := by
  rw [selfPlay]
  have h_len : (List.ofFn fun i : Fin t => sms i).length = t := by simp
  rw [h_len]
  exact selfPlayAux_ofFn σ sms t t (le_refl t)

/-- The replay of a strategy plays exactly what the strategy plays. -/
lemma playClient_replayStrategy (σ : ClientStrategy) (sms : ℕ → ServerMove) (t : ℕ) :
    playClient (replayStrategy σ) sms t = playClient σ sms t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero =>
      simp [playClient, replayStrategy, selfPlay, selfPlayAux]
    | succ t =>
      rw [playClient, playClient]
      have h1 : (List.ofFn fun (i : Fin (t + 1)) => playClient (replayStrategy σ) sms ↑i) =
        List.ofFn fun (i : Fin (t + 1)) => playClient σ sms ↑i := by
        congr
        funext x
        exact ih x.val x.isLt
      rw [h1, replayStrategy, selfPlay_ofFn]

/-- The replay of a strategy does not look at the recorded client history. -/
lemma replayStrategy_indep_client_history (σ : ClientStrategy)
    (cs cs' : List ClientMove) (ss : List ServerMove) :
    replayStrategy σ (cs, ss) = replayStrategy σ (cs', ss) := rfl

/-- `selfPlayAux` as a `Nat.rec` iteration, the shape `Computable.nat_rec` supports. -/
lemma selfPlayAux_eq_rec (σ : ClientStrategy) (ss : List ServerMove) (n : ℕ) :
    selfPlayAux σ ss n =
      Nat.rec ([] : List ClientMove) (fun y IH => IH ++ [σ (IH, ss.take y)]) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [selfPlayAux, ih]

/-- Replaying a computable family of strategies is computable. -/
lemma computable₂_selfPlay {σ' : ℕ → ClientStrategy} (h : Computable₂ σ') :
    Computable₂ (fun d ss => selfPlay (σ' d) ss) := by
  have hstep : Computable₂ (fun (a : ℕ × List ServerMove) (p : ℕ × List ClientMove) =>
      p.2 ++ [σ' a.1 (p.2, a.2.take p.1)]) := by
    have hσ : Computable (fun q : (ℕ × List ServerMove) × (ℕ × List ClientMove) =>
        σ' q.1.1 (q.2.2, q.1.2.take q.2.1)) :=
      h.comp (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.snd.comp Computable.snd)
          (Primrec.list_take.to_comp.comp (Computable.snd.comp Computable.fst)
            (Computable.fst.comp Computable.snd)))
    exact Computable.list_concat.comp (Computable.snd.comp Computable.snd) hσ
  have hrec := Computable.nat_rec (f := fun a : ℕ × List ServerMove => a.2.length)
    (g := fun _ : ℕ × List ServerMove => ([] : List ClientMove))
    (Computable.list_length.comp Computable.snd) (Computable.const _) hstep
  refine hrec.of_eq ?_
  rintro ⟨d, ss⟩
  exact (selfPlayAux_eq_rec _ _ _).symm

/-- The replay of a computable family of strategies is computable. -/
lemma computable₂_replayStrategy {σ' : ℕ → ClientStrategy} (h : Computable₂ σ') :
    Computable₂ (fun d => replayStrategy (σ' d)) := by
  have hself := computable₂_selfPlay h
  exact h.comp Computable.fst
    (Computable.pair
      (hself.comp Computable.fst (Computable.snd.comp Computable.snd))
      (Computable.snd.comp Computable.snd))

end Kolmogorov
