import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.ZMod.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Partrec
import Mathlib.Algebra.Field.ZMod
import KolmogorovMathlib.CommonInformation.AffineIncidence
import KolmogorovMathlib.Foundation.PrimrecExtras

namespace Kolmogorov

def primeTest (p : Nat) : Bool :=
  decide (2 ≤ p ∧ ∀ d < p, d < 2 ∨ p % d ≠ 0)

lemma primeTest_primrec : Primrec primeTest := by
  have hgood : PrimrecRel (fun d p : Nat => d < 2 ∨ p % d ≠ 0) :=
    PrimrecPred.or
      (Primrec.nat_lt.comp Primrec.fst (Primrec.const 2))
      ((Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst)
        (Primrec.const 0)).not)
  have hall : PrimrecPred (fun p : Nat => ∀ d < p, d < 2 ∨ p % d ≠ 0) :=
    hgood.forall_lt.comp Primrec.id Primrec.id
  exact ((Primrec.nat_le.comp (Primrec.const 2) Primrec.id).and hall).decide

lemma primeTest_eq_true_iff {p : Nat} : primeTest p = true ↔ Nat.Prime p := by
  rw [show primeTest p = decide (2 ≤ p ∧ ∀ d < p, d < 2 ∨ p % d ≠ 0) by rfl]
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨hp2, hfree⟩
    by_contra hnprime
    obtain ⟨d, hdvd, hd2, hdp⟩ :=
      (Nat.not_prime_iff_exists_dvd_lt hp2).mp hnprime
    rcases hfree d hdp with hdlt | hmod
    · omega
    · exact hmod (Nat.mod_eq_zero_of_dvd hdvd)
  · intro hp
    refine ⟨hp.two_le, fun d hdp => ?_⟩
    by_cases hd2 : d < 2
    · exact Or.inl hd2
    · right
      intro hmod
      have hdvd : d ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hmod
      exact hdp.ne (hp.eq_one_or_self_of_dvd d hdvd |>.resolve_left (by omega))

/-- The explicit Bertrand interval searched for the concrete prime. -/
def primeWindow (n : Nat) : List Nat :=
  (List.range (2 ^ (n + 1) + 1)).drop (2 ^ n + 1)

lemma primeWindow_mem_iff {p n : Nat} :
  p ∈ (List.range (2 ^ (n + 1) + 1)).drop (2 ^ n + 1) ↔
    2 ^ n < p ∧ p ≤ 2 ^ (n + 1) := by
  rw [List.mem_drop_iff_getElem]
  constructor
  · rintro ⟨j, hj, heq⟩
    rw [List.getElem_range] at heq
    simp only [List.length_range] at hj
    omega
  · rintro ⟨hlow, hupp⟩
    refine ⟨p - (2 ^ n + 1), ?_, ?_⟩
    · simp only [List.length_range]
      omega
    · rw [List.getElem_range]
      omega

lemma exists_prime_pow_two_window (n : Nat) :
  ∃ p, Nat.Prime p ∧ 2 ^ n < p ∧ p ≤ 2 ^ (n + 1) := by
  obtain ⟨p, hp, hlower, hupper⟩ := Nat.bertrand (2 ^ n) (by positivity)
  refine ⟨p, hp, hlower, ?_⟩
  simpa [pow_succ, mul_comm] using hupper

/-- The first prime in `primeWindow n`, with an unreachable default branch. -/
def concretePrime (n : Nat) : Nat :=
  (primeWindow n).find? primeTest |>.getD 2

private lemma primeWindow_find_primrec :
    Primrec fun n => (primeWindow n).find? primeTest := by
  have hpow : Primrec fun n : Nat => 2 ^ n := by
    rw [Primrec.nat_iff]
    convert Nat.Primrec.pow.comp
      (Nat.Primrec.pair (Nat.Primrec.const 2) Nat.Primrec.id) using 1
    simp
  have hwindow : Primrec primeWindow := by
    exact Primrec.list_drop.comp
      (Primrec.succ.comp hpow)
      (Primrec.list_range.comp
        (Primrec.succ.comp (hpow.comp (Primrec.succ.comp Primrec.id))))
  have hstep : Primrec₂
      (fun (_n : Nat) (q : Nat × Option Nat) =>
        bif primeTest q.1 then some q.1 else q.2) :=
    (Primrec.cond
      (primeTest_primrec.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have heq (l : List Nat) :
      l.foldr (fun p out => bif primeTest p then some p else out) none =
        l.find? primeTest := by
    induction l with
    | nil => rfl
    | cons p l ih =>
        simp only [List.foldr_cons, ih]
        cases hp : primeTest p <;> simp [List.find?, hp]
  exact (Primrec.list_foldr hwindow (Primrec.const none) hstep).of_eq
    (fun n => heq (primeWindow n))

lemma boundedPrimeSearch_primrec : Primrec concretePrime := by
  exact (Primrec.option_getD.comp primeWindow_find_primrec (Primrec.const 2)).of_eq
    (fun _ => rfl)

lemma concretePrime_spec (n : Nat) :
    Nat.Prime (concretePrime n) ∧ 2 ^ n < concretePrime n ∧
      concretePrime n ≤ 2 ^ (n + 1) := by
  obtain ⟨p, hp, hlower, hupper⟩ := exists_prime_pow_two_window n
  have hpwindow : p ∈ primeWindow n := by
    exact primeWindow_mem_iff.mpr ⟨hlower, hupper⟩
  have hptest : primeTest p = true := primeTest_eq_true_iff.mpr hp
  have hisSome : ((primeWindow n).find? primeTest).isSome = true :=
    List.find?_isSome.mpr ⟨p, hpwindow, hptest⟩
  cases hfind : (primeWindow n).find? primeTest with
  | none => simp [hfind] at hisSome
  | some q =>
      have hqprime : Nat.Prime q :=
        primeTest_eq_true_iff.mp (List.find?_some hfind)
      have hqmem : q ∈ primeWindow n := by
        obtain ⟨_, i, hi, heq, _⟩ :=
          List.find?_eq_some_iff_getElem.mp hfind
        exact List.mem_of_getElem heq
      have hqwindow : 2 ^ n < q ∧ q ≤ 2 ^ (n + 1) :=
        primeWindow_mem_iff.mp hqmem
      simpa [concretePrime, hfind] using ⟨hqprime, hqwindow⟩

lemma concretePrime_prime (n : Nat) : Nat.Prime (concretePrime n) :=
  (concretePrime_spec n).1

lemma concretePrime_lower (n : Nat) : 2 ^ n < concretePrime n :=
  (concretePrime_spec n).2.1

lemma concretePrime_upper (n : Nat) : concretePrime n ≤ 2 ^ (n + 1) :=
  (concretePrime_spec n).2.2

lemma concretePrime_computable : Computable concretePrime :=
  boundedPrimeSearch_primrec.to_comp

abbrev ConcreteField (n : Nat) := ZMod (concretePrime n)

instance (n : Nat) : Fact (Nat.Prime (concretePrime n)) := ⟨concretePrime_prime n⟩

lemma concreteField_card_eq (n : Nat) :
  Fintype.card (ConcreteField n) = concretePrime n :=
  ZMod.card (concretePrime n)

lemma concreteField_card_bounds (n : Nat) :
  2 ^ n < Fintype.card (ConcreteField n) ∧
  Fintype.card (ConcreteField n) ≤ 2 ^ (n + 1) := by
  rw [concreteField_card_eq]
  exact ⟨concretePrime_lower n, concretePrime_upper n⟩

lemma concreteIncidentEdges_noFourCycle (n : Nat) :
    NoFourCycle (AffineIncidence.Incident (F := ConcreteField n)) :=
  AffineIncidence.noFourCycle

lemma concreteIncidentEdges_card_bounds (n : Nat) :
  2 ^ (3 * n) < (AffineIncidence.incidentEdges (ConcreteField n)).card ∧
  (AffineIncidence.incidentEdges (ConcreteField n)).card ≤ 2 ^ (3 * n + 3) := by
  rw [AffineIncidence.incidentEdges_card, concreteField_card_eq]
  constructor
  · rw [show 2 ^ (3 * n) = (2 ^ n) ^ 3 by
      rw [← pow_mul]
      congr 1
      omega]
    exact Nat.pow_lt_pow_left (concretePrime_lower n) (by omega)
  · calc
      concretePrime n ^ 3 ≤ (2 ^ (n + 1)) ^ 3 :=
        Nat.pow_le_pow_left (concretePrime_upper n) 3
      _ = 2 ^ (3 * n + 3) := by
        rw [← pow_mul]
        congr 1
        omega

end Kolmogorov
