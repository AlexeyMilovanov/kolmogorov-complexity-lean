import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Complexity.LayeredDecompressors
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Interface.Dovetailing
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Reduce
import Mathlib.Data.Nat.Dist

/-!
# Complexity over a `q`-letter alphabet

`abs_qPlainK_mul_logb_sub_cVal_le` (SUV Exercise 5): for an alphabet of size `q ≥ 2`, the
`q`-ary complexity rescaled by `log₂ q` differs from the binary complexity by at most a
constant — `C_q(x) · log₂ q = C(x) + O(1)`.

The two directions are `natLog_mul_logb_sub_le` and `sub_natLog_mul_logb_le`, each obtained by
translating descriptions between the alphabets: `encodeBitsQ` and `decodeBitsQ` convert
between bit strings and `q`-ary strings with the length relation `encodeBitsQ_length`, and
`geomQ`, `qValQ`, `qToNatQ` and `binToNatQ` are the numeral arithmetic behind them.  The
remaining lemmas compare `Nat.log q` with `Real.logb q` closely enough for the rescaling to be
exact up to a constant.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- **Exercise 5.** For an arbitrary alphabet of size `q ≥ 2` the `q`-ary
complexity equals `C(x) / log q` up to an additive constant. -/
private def geomQ (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => geomQ q n + q ^ n

private lemma geom_formulaQ (q : ℕ) (hq : 2 ≤ q) (n : ℕ) :
    (q - 1) * geomQ q n = q ^ n - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [geomQ]
    rw [Nat.mul_add]
    have ih' : (k + 1) * geomQ (k + 2) n = (k + 2) ^ n - 1 := ih
    rw [ih']
    have h1 : 1 ≤ (k + 2) ^ n := Nat.one_le_pow n (k + 2) (by omega)
    calc (k + 2) ^ n - 1 + (k + 1) * (k + 2) ^ n
      _ = (k + 2) ^ n + (k + 1) * (k + 2) ^ n - 1 := by omega
      _ = (k + 2) * (k + 2) ^ n - 1 := by ring_nf
      _ = (k + 2) ^ (n + 1) - 1 := by rw [Nat.pow_succ']

private def qValQ (q : ℕ) : List (Fin q) → ℕ
  | [] => 0
  | a :: w => a.val + q * qValQ q w

private lemma qVal_ltQ (q : ℕ) (w : List (Fin q)) :
    qValQ q w < q ^ w.length := by
  induction w with
  | nil => dsimp [qValQ]; omega
  | cons a w ih =>
    dsimp [qValQ]
    have h_a := a.isLt
    calc a.val + q * qValQ q w
      _ < q + q * qValQ q w := by omega
      _ = q * (qValQ q w + 1) := by ring
      _ ≤ q * q ^ w.length := Nat.mul_le_mul_left q ih
      _ = q ^ (w.length + 1) := by rw [Nat.pow_succ']

private def qToNatQ (q : ℕ) (w : List (Fin q)) : ℕ :=
  geomQ q w.length + qValQ q w

private lemma qToNat_boundQ (q : ℕ) (hq : 2 ≤ q) (w : List (Fin q)) :
    (q - 1) * qToNatQ q w + 1 < q ^ (w.length + 1) := by
  dsimp [qToNatQ]
  rw [Nat.mul_add, geom_formulaQ q hq w.length]
  have h_qVal := qVal_ltQ q w
  have h_sub : 1 ≤ q ^ w.length := Nat.one_le_pow w.length q (by omega)
  have h_qVal_mul : (q - 1) * qValQ q w < (q - 1) * q ^ w.length :=
    Nat.mul_lt_mul_of_pos_left h_qVal (by omega)
  calc q ^ w.length - 1 + (q - 1) * qValQ q w + 1
    _ = q ^ w.length + (q - 1) * qValQ q w := by omega
    _ < q ^ w.length + (q - 1) * q ^ w.length := by omega
    _ = (q - 1) * q ^ w.length + q ^ w.length := by ring
    _ = q * q ^ w.length := by
      cases q with
      | zero => omega
      | succ q => dsimp; ring
    _ = q ^ (w.length + 1) := by rw [Nat.pow_succ']

private def decodeBitsQ : BitString → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * decodeBitsQ bs

private lemma decodeBitsQ_lt_pow (p : BitString) :
    decodeBitsQ p < 2 ^ p.length := by
  induction p with
  | nil => dsimp [decodeBitsQ]; omega
  | cons b bs ih =>
    dsimp [decodeBitsQ]
    split <;> omega

private def binToNatQ (p : BitString) : ℕ :=
  2 ^ p.length - 1 + decodeBitsQ p

private def encodeBitsQ : ℕ → ℕ → BitString
  | 0, _ => []
  | k + 1, n => (n % 2 == 1) :: encodeBitsQ k (n / 2)

private lemma encodeBitsQ_length (k n : ℕ) : (encodeBitsQ k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => dsimp [encodeBitsQ]; rw [ih]

private def natToBinQ (n : ℕ) : BitString :=
  let L := Nat.log 2 (n + 1)
  encodeBitsQ L (n - (2 ^ L - 1))

private lemma natToBinQ_length (n : ℕ) :
    (natToBinQ n).length = Nat.log 2 (n + 1) := by
  dsimp [natToBinQ]
  exact encodeBitsQ_length _ _

private lemma decodeBitsQ_encodeBitsQ (k n : ℕ) :
    decodeBitsQ (encodeBitsQ k n) = n % 2 ^ k := by
  induction k generalizing n with
  | zero => dsimp [encodeBitsQ, decodeBitsQ]; omega
  | succ k ih =>
    have h1 : n % (2 * 2 ^ k) = n % 2 + 2 * (n / 2 % 2 ^ k) := by
      calc n % (2 * 2 ^ k)
        _ = 2 * (n % (2 * 2 ^ k) / 2) + n % (2 * 2 ^ k) % 2 :=
          (Nat.div_add_mod (n % (2 * 2 ^ k)) 2).symm
        _ = 2 * (n / 2 % 2 ^ k) + n % 2 := by
          rw [Nat.mod_mul_right_div_self]
          rw [Nat.mod_mod_of_dvd n (Nat.dvd_mul_right 2 (2 ^ k))]
        _ = n % 2 + 2 * (n / 2 % 2 ^ k) := Nat.add_comm _ _
    have h_bit : (if n % 2 == 1 then 1 else 0) = n % 2 := by
      have : n % 2 = 0 ∨ n % 2 = 1 := by
        have := Nat.mod_lt n (by decide : 0 < 2)
        omega
      rcases this with h | h <;> rw [h] <;> rfl
    calc decodeBitsQ (encodeBitsQ (k + 1) n)
      _ = (if n % 2 == 1 then 1 else 0) + 2 * decodeBitsQ (encodeBitsQ k (n / 2)) := by
        dsimp [encodeBitsQ, decodeBitsQ]
      _ = (n % 2) + 2 * (n / 2 % 2 ^ k) := by rw [ih, h_bit]
      _ = n % (2 * 2 ^ k) := h1.symm
      _ = n % 2 ^ (k + 1) := by rw [Nat.pow_succ']

private lemma binToNatQ_natToBinQ (n : ℕ) :
    binToNatQ (natToBinQ n) = n := by
  dsimp [binToNatQ, natToBinQ]
  generalize hL : Nat.log 2 (n + 1) = L
  have h_len : (encodeBitsQ L (n - (2 ^ L - 1))).length = L := encodeBitsQ_length L _
  rw [h_len]
  rw [decodeBitsQ_encodeBitsQ]
  have h_lb : 2 ^ L ≤ n + 1 := by
    rw [← hL]
    exact Nat.pow_log_le_self 2 (by omega)
  have h_ub : n + 1 < 2 ^ (L + 1) := by
    rw [← hL]
    exact Nat.lt_pow_succ_log_self (by decide) (n + 1)
  have h_m_lt : n - (2 ^ L - 1) < 2 ^ L := by
    have : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [Nat.pow_succ']
    omega
  rw [Nat.mod_eq_of_lt h_m_lt]
  have : 2 ^ L - 1 ≤ n := by omega
  omega

private lemma encodeBitsQ_decodeBitsQ (p : BitString) :
    encodeBitsQ p.length (decodeBitsQ p) = p := by
  induction p with
  | nil => rfl
  | cons b bs ih =>
    cases b
    · dsimp [decodeBitsQ, encodeBitsQ]
      have h1 : (0 + 2 * decodeBitsQ bs) / 2 = decodeBitsQ bs := by omega
      have h2 : ((0 + 2 * decodeBitsQ bs) % 2 == 1) = false := by
        have : (0 + 2 * decodeBitsQ bs) % 2 = 0 := by omega
        rw [this]
        rfl
      rw [h1, h2, ih]
    · dsimp [decodeBitsQ, encodeBitsQ]
      have h1 : (1 + 2 * decodeBitsQ bs) / 2 = decodeBitsQ bs := by omega
      have h2 : ((1 + 2 * decodeBitsQ bs) % 2 == 1) = true := by
        have : (1 + 2 * decodeBitsQ bs) % 2 = 1 := by omega
        rw [this]
        rfl
      rw [h1, h2, ih]

private lemma natToBinQ_binToNatQ (p : BitString) :
    natToBinQ (binToNatQ p) = p := by
  dsimp [natToBinQ]
  have h_len : Nat.log 2 (binToNatQ p + 1) = p.length := by
    have h_lb : 2 ^ p.length ≤ binToNatQ p + 1 := by
      dsimp [binToNatQ]
      have : 1 ≤ 2 ^ p.length := Nat.one_le_pow p.length 2 (by omega)
      omega
    have h_ub : binToNatQ p + 1 < 2 ^ (p.length + 1) := by
      dsimp [binToNatQ]
      have hd := decodeBitsQ_lt_pow p
      omega
    have hn : binToNatQ p + 1 ≠ 0 := by omega
    exact (Nat.log_eq_iff (Or.inr ⟨by decide, hn⟩)).mpr ⟨h_lb, h_ub⟩
  rw [h_len]
  have h_sub : binToNatQ p - (2 ^ p.length - 1) = decodeBitsQ p := by
    dsimp [binToNatQ]
    omega
  rw [h_sub]
  exact encodeBitsQ_decodeBitsQ p

private def natToQDigitsQ (q : ℕ) (hq : 2 ≤ q) : ℕ → ℕ → List (Fin q)
  | 0, _ => []
  | k + 1, n => ⟨n % q, Nat.mod_lt _ (by omega)⟩ :: natToQDigitsQ q hq k (n / q)

private lemma natToQDigitsQ_length (q : ℕ) (hq : 2 ≤ q) (k n : ℕ) :
    (natToQDigitsQ q hq k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    dsimp [natToQDigitsQ]
    rw [ih]

private def natToQQ (q : ℕ) (hq : 2 ≤ q) (n : ℕ) : List (Fin q) :=
  let L := Nat.log q ((q - 1) * n + 1)
  natToQDigitsQ q hq L (n - geomQ q L)

private lemma natToQQ_length (q : ℕ) (hq : 2 ≤ q) (n : ℕ) :
    (natToQQ q hq n).length = Nat.log q ((q - 1) * n + 1) := by
  dsimp [natToQQ]
  exact natToQDigitsQ_length q hq _ _

private lemma qValQ_natToQDigitsQ (q : ℕ) (hq : 2 ≤ q) (k m : ℕ) :
    qValQ q (natToQDigitsQ q hq k m) = m % q ^ k := by
  induction k generalizing m with
  | zero => dsimp [natToQDigitsQ, qValQ]; omega
  | succ k ih =>
    dsimp [natToQDigitsQ, qValQ]
    rw [ih (m / q)]
    have h1 : m % (q * q ^ k) = m % q + q * (m / q % q ^ k) := by
      have h_mod : m % (q * q ^ k) = q * (m % (q * q ^ k) / q) + m % (q * q ^ k) % q :=
        (Nat.div_add_mod (m % (q * q ^ k)) q).symm
      rw [Nat.mod_mul_right_div_self] at h_mod
      rw [Nat.mod_mod_of_dvd m (Nat.dvd_mul_right q (q ^ k))] at h_mod
      omega
    rw [← h1, Nat.pow_succ']

private lemma natToQDigitsQ_qValQ (q : ℕ) (hq : 2 ≤ q) (w : List (Fin q)) :
    natToQDigitsQ q hq w.length (qValQ q w) = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    dsimp [qValQ, natToQDigitsQ]
    have h1 : (a.val + q * qValQ q w) % q = a.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
    have h2 : (a.val + q * qValQ q w) / q = qValQ q w := by
      calc (a.val + q * qValQ q w) / q
        _ = (a.val + qValQ q w * q) / q := by rw [Nat.mul_comm q]
        _ = a.val / q + qValQ q w := Nat.add_mul_div_right a.val (qValQ q w) (by omega)
        _ = 0 + qValQ q w := by rw [Nat.div_eq_of_lt a.isLt]
        _ = qValQ q w := by omega
    have h_a_eq : (⟨(a.val + q * qValQ q w) % q, Nat.mod_lt _ (by omega)⟩ : Fin q) = a := by
      ext
      dsimp
      exact h1
    rw [h_a_eq, h2, ih]

private lemma qToNatQ_natToQQ (q : ℕ) (hq : 2 ≤ q) (n : ℕ) :
    qToNatQ q (natToQQ q hq n) = n := by
  dsimp [qToNatQ, natToQQ]
  rw [natToQDigitsQ_length]
  set L := Nat.log q ((q - 1) * n + 1)
  rw [qValQ_natToQDigitsQ]
  have h_m_lt : n - geomQ q L < q ^ L := by
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
    have h_log_ub : (k + 1) * n + 1 < (k + 2) ^ (L + 1) := Nat.lt_pow_succ_log_self (by omega) _
    have h_log_lb : (k + 2) ^ L ≤ (k + 1) * n + 1 := Nat.pow_log_le_self (k + 2) (by omega)
    have h_geom : (k + 1) * geomQ (k + 2) L = (k + 2) ^ L - 1 := by
      have hg := geom_formulaQ (k + 2) (by omega) L
      have : k + 2 - 1 = k + 1 := by omega
      rwa [this] at hg
    have h_pow1 : 1 ≤ (k + 2) ^ L := Nat.one_le_pow L (k + 2) (by omega)
    have h_lt : (k + 1) * (n - geomQ (k + 2) L) < (k + 1) * (k + 2) ^ L := by
      rw [Nat.mul_sub_left_distrib, h_geom]
      have h_le : (k + 2) ^ L - 1 ≤ (k + 1) * n := by omega
      have h_ub : (k + 1) * n < (k + 2) ^ (L + 1) - 1 := by omega
      have h_sub_lt : (k + 1) * n - ((k + 2) ^ L - 1) <
          (k + 2) ^ (L + 1) - 1 - ((k + 2) ^ L - 1) := by omega
      have h_eq : (k + 2) ^ (L + 1) - 1 - ((k + 2) ^ L - 1) = (k + 1) * (k + 2) ^ L := by
        have h1 : 1 ≤ (k + 2) ^ L := h_pow1
        have h2 : (k + 2) ^ L ≤ (k + 2) ^ (L + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have h3 : (k + 2) ^ (L + 1) = (k + 1) * (k + 2) ^ L + (k + 2) ^ L := by
          rw [Nat.pow_succ']
          ring
        omega
      omega
    exact Nat.lt_of_mul_lt_mul_left h_lt
  rw [Nat.mod_eq_of_lt h_m_lt]
  have h_geom_le : geomQ q L ≤ n := by
    have h_log_lb : q ^ L ≤ (q - 1) * n + 1 := Nat.pow_log_le_self q (by omega)
    have h_geom := geom_formulaQ q hq L
    have h_mul : (q - 1) * geomQ q L ≤ (q - 1) * n := by omega
    exact Nat.le_of_mul_le_mul_left h_mul (by omega)
  omega

private lemma natToQQ_qToNatQ (q : ℕ) (hq : 2 ≤ q) (w : List (Fin q)) :
    natToQQ q hq (qToNatQ q w) = w := by
  dsimp [natToQQ]
  have h_len : Nat.log q ((q - 1) * qToNatQ q w + 1) = w.length := by
    have h_lb : q ^ w.length ≤ (q - 1) * qToNatQ q w + 1 := by
      dsimp [qToNatQ]
      rw [Nat.mul_add, geom_formulaQ q hq w.length]
      have : 1 ≤ q ^ w.length := Nat.one_le_pow w.length q (by omega)
      omega
    have h_ub : (q - 1) * qToNatQ q w + 1 < q ^ (w.length + 1) := qToNat_boundQ q hq w
    have hn : (q - 1) * qToNatQ q w + 1 ≠ 0 := by omega
    exact (Nat.log_eq_iff (Or.inr ⟨by omega, hn⟩)).mpr ⟨h_lb, h_ub⟩
  rw [h_len]
  have h_sub : qToNatQ q w - geomQ q w.length = qValQ q w := by
    dsimp [qToNatQ]
    omega
  rw [h_sub]
  exact natToQDigitsQ_qValQ q hq w

private noncomputable def mapToQQ (q : ℕ) (U : Map) : QMap q := fun pr =>
  U (natToBinQ (qToNatQ q pr.1), pr.2)

private noncomputable def mapToBinQ (q : ℕ) (hq : 2 ≤ q) (D : QMap q) : Map := fun pr =>
  D (natToQQ q hq (binToNatQ pr.1), pr.2)

private def natLogRecQ (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if q ^ (natLogRecQ q n + 1) ≤ n + 1 then natLogRecQ q n + 1 else natLogRecQ q n

private lemma natLogRec_eq_logQ (q n : ℕ) (hq : 2 ≤ q) :
    natLogRecQ q n = Nat.log q n := by
  induction n with
  | zero =>
    dsimp [natLogRecQ]
    cases q with
    | zero => rfl
    | succ q => cases q with | zero => rfl | succ q => rfl
  | succ n ih =>
    dsimp [natLogRecQ]
    rw [ih]
    have hn : n + 1 ≠ 0 := by omega
    have h_log_le : ∀ (m k : ℕ), m ≤ q ^ k → Nat.log q m ≤ k := by
      intro m k h
      by_contra h_not
      have hm : m ≠ 0 := by
        rintro rfl
        have : Nat.log q 0 = 0 := by rcases q with _ | _ | q <;> rfl
        omega
      have hk1 : k + 1 ≤ Nat.log q m := by omega
      have h1 : q ^ (k + 1) ≤ m := Nat.pow_le_of_le_log hm hk1
      have h2 : q ^ k < q ^ (k + 1) :=
        Nat.pow_lt_pow_right (by omega : 1 < q) (by omega : k < k + 1)
      exact Nat.not_le_of_gt h2 (h1.trans h)
    split_ifs with h
    · have h_eq : Nat.log q (n + 1) = Nat.log q n + 1 := by
        have h_le1 : Nat.log q n + 1 ≤ Nat.log q (n + 1) := Nat.le_log_of_pow_le (by omega) h
        have h_lt : n < q ^ (Nat.log q n + 1) := Nat.lt_pow_succ_log_self (by omega) n
        have h_le2 : Nat.log q (n + 1) ≤ Nat.log q n + 1 :=
          h_log_le (n + 1) (Nat.log q n + 1) (by omega)
        omega
      exact h_eq.symm
    · have h_eq : Nat.log q (n + 1) = Nat.log q n := by
        have h_lt : Nat.log q (n + 1) < Nat.log q n + 1 := by
          by_contra h_not
          have h_le : Nat.log q n + 1 ≤ Nat.log q (n + 1) := by omega
          have h_pow_le : q ^ (Nat.log q n + 1) ≤ n + 1 := Nat.pow_le_of_le_log (by omega) h_le
          contradiction
        have h_mono : Nat.log q n ≤ Nat.log q (n + 1) :=
          Nat.log_mono (by omega) (by omega) (by omega)
        omega
      exact h_eq.symm

private lemma primrec_natLogRecQ (q : ℕ) : Primrec (natLogRecQ q) := by
  have h_f : Primrec (fun _ : Unit => 0) := Primrec.const 0
  have h_g : Primrec₂ (fun (_ : Unit) (p : ℕ × ℕ) =>
      if q ^ (p.2 + 1) ≤ p.1 + 1 then p.2 + 1 else p.2) := by
    have h_pow : Primrec (fun p : Unit × ℕ × ℕ => q ^ (p.2.2 + 1)) := by
      have h1 : Primrec (fun p : Unit × ℕ × ℕ => q) := Primrec.const q
      have h2 : Primrec (fun p : Unit × ℕ × ℕ => p.2.2 + 1) :=
        Primrec.succ.comp (Primrec.snd.comp Primrec.snd)
      exact nat_pow_primrec₂.comp h1 h2
    have h_succ_n : Primrec (fun p : Unit × ℕ × ℕ => p.2.1 + 1) :=
      Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
    have h_succ_ih : Primrec (fun p : Unit × ℕ × ℕ => p.2.2 + 1) :=
      Primrec.succ.comp (Primrec.snd.comp Primrec.snd)
    have h_ih : Primrec (fun p : Unit × ℕ × ℕ => p.2.2) :=
      Primrec.snd.comp Primrec.snd
    exact (Primrec.ite (Primrec.nat_le.comp h_pow h_succ_n) h_succ_ih h_ih).to₂
  have h_rec := Primrec.nat_rec h_f h_g
  exact (h_rec.comp (Primrec.const ()) Primrec.id).of_eq (fun l => by
    change Nat.rec 0 (fun n IH => if q ^ (IH + 1) ≤ n + 1 then IH + 1 else IH) l = natLogRecQ q l
    induction l with
    | zero => rfl
    | succ l ih => dsimp [natLogRecQ]; rw [ih])

private lemma computable_nat_logQ (q : ℕ) (hq : 2 ≤ q) : Computable (Nat.log q) :=
  (primrec_natLogRecQ q).to_comp.of_eq (fun n => natLogRec_eq_logQ q n hq)

private lemma primrecDecodeBitsQ : Primrec decodeBitsQ := by
  have h_g : Primrec₂ (fun (_ : BitString) (p : Bool × ℕ) => (if p.1 then 1 else 0) + 2 * p.2) := by
    have h_b : Primrec (fun p : BitString × Bool × ℕ => if p.2.1 then 1 else 0) :=
      Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const true))
        (Primrec.const 1) (Primrec.const 0)
    have h_acc : Primrec (fun p : BitString × Bool × ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
    exact Primrec.nat_add.comp h_b (Primrec.nat_mul.comp (Primrec.const 2) h_acc)
  have h_fold := Primrec.list_foldr Primrec.id (Primrec.const 0) h_g
  exact h_fold.of_eq (fun bs => by
    change List.foldr (fun b s => (if b then 1 else 0) + 2 * s) 0 bs = decodeBitsQ bs
    induction bs with
    | nil => rfl
    | cons b bs ih => dsimp [decodeBitsQ]; rw [ih])

private lemma primrec_geomQ (q : ℕ) : Primrec (geomQ q) := by
  have h_f : Primrec (fun _ : Unit => 0) := Primrec.const 0
  have h_g : Primrec₂ (fun (_ : Unit) (p : ℕ × ℕ) => p.2 + q ^ p.1) := by
    have h1 : Primrec (fun p : Unit × ℕ × ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
    have h2 : Primrec (fun p : Unit × ℕ × ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
    have h3 : Primrec (fun p : Unit × ℕ × ℕ => q ^ p.2.1) :=
      nat_pow_primrec₂.comp (Primrec.const q) h2
    exact Primrec.nat_add.comp h1 h3
  have h_rec := Primrec.nat_rec h_f h_g
  have h_eq : (fun l : ℕ => Nat.rec 0 (fun n IH => IH + q ^ n) l) = geomQ q := by
    funext l
    induction l with
    | zero => rfl
    | succ l ih => dsimp [geomQ]; rw [ih]
  exact (h_rec.comp (Primrec.const ()) Primrec.id).of_eq (fun l => by
    change Nat.rec 0 (fun n IH => IH + q ^ n) l = geomQ q l
    rw [congr_fun h_eq l])

private lemma primrec_qValQ (q : ℕ) : Primrec (qValQ q) := by
  have h_step : Primrec₂ (fun (_ : List (Fin q)) (p : Fin q × ℕ) => p.1.val + q * p.2) := by
    have h_a : Primrec (fun p : List (Fin q) × Fin q × ℕ => p.2.1.val) :=
      Primrec.fin_val.comp (Primrec.fst.comp Primrec.snd)
    have h_acc : Primrec (fun p : List (Fin q) × Fin q × ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
    exact Primrec.nat_add.comp h_a (Primrec.nat_mul.comp (Primrec.const q) h_acc)
  have h_fold := Primrec.list_foldr Primrec.id (Primrec.const 0) h_step
  exact h_fold.of_eq (fun w => by
    change List.foldr (fun a s => a.val + q * s) 0 w = qValQ q w
    induction w with
    | nil => rfl
    | cons a w ih => dsimp [qValQ]; rw [ih])

private lemma primrec_qToNatQ (q : ℕ) : Primrec (qToNatQ q) := by
  exact Primrec.nat_add.comp
    ((primrec_geomQ q).comp Primrec.list_length)
    (primrec_qValQ q)

private lemma primrec_binToNatQ : Primrec binToNatQ := by
  have h1 : Primrec (fun p : BitString => 2 ^ p.length - 1) :=
    Primrec.nat_sub.comp
      (nat_pow_primrec₂.comp (Primrec.const 2) Primrec.list_length)
      (Primrec.const 1)
  exact Primrec.nat_add.comp h1 primrecDecodeBitsQ

private lemma encodeBitsQ_eq_range_map (k n : ℕ) :
    encodeBitsQ k n = (List.range k).map (fun i => n / 2 ^ i % 2 == 1) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    dsimp [encodeBitsQ]
    rw [ih (n / 2)]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    dsimp [Function.comp]
    congr 1
    · simp
    · congr 1; ext i
      dsimp [Function.comp]
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul]

private lemma primrec_encodeBitsQ : Primrec₂ encodeBitsQ := by
  have h_range : Primrec (fun p : ℕ × ℕ => List.range p.1) :=
    Primrec.list_range.comp Primrec.fst
  have h_n : Primrec (fun p : (ℕ × ℕ) × ℕ => p.1.2) := Primrec.snd.comp Primrec.fst
  have h_i : Primrec (fun p : (ℕ × ℕ) × ℕ => p.2) := Primrec.snd
  have h_pow := nat_pow_primrec₂.comp (Primrec.const 2) h_i
  have h_div := Primrec.nat_div.comp h_n h_pow
  have h_mod := Primrec.nat_mod.comp h_div (Primrec.const 2)
  have h_elem : Primrec₂ (fun (p : ℕ × ℕ) (i : ℕ) => p.2 / 2 ^ i % 2 == 1) :=
    (Primrec.beq.comp h_mod (Primrec.const 1)).to₂
  have h_map := Primrec.list_map h_range h_elem
  exact (h_map.of_eq (fun p => (encodeBitsQ_eq_range_map p.1 p.2).symm)).to₂

private lemma computable_natToBinQ : Computable natToBinQ := by
  have h_log : Computable (fun n : ℕ => Nat.log 2 (n + 1)) := by
    have h_arg : Primrec (fun n : ℕ => n + 1) := Primrec.nat_add.comp Primrec.id (Primrec.const 1)
    exact (computable_nat_logQ 2 (by decide)).comp h_arg.to_comp
  have h_sub : Computable (fun n : ℕ => n - (2 ^ Nat.log 2 (n + 1) - 1)) := by
    have h_pow := Computable₂.comp nat_pow_primrec₂.to_comp (Computable.const 2) h_log
    have h_pow_sub := Computable₂.comp Primrec.nat_sub.to_comp h_pow (Computable.const 1)
    exact Computable₂.comp Primrec.nat_sub.to_comp Computable.id h_pow_sub
  exact Computable₂.comp primrec_encodeBitsQ.to_comp h_log h_sub

private lemma mapToQ_partrecQ (q : ℕ) (U : Map) (hU : Partrec U) :
    Partrec (mapToQQ q U) := by
  have h_f : Computable (fun (pr : List (Fin q) × BitString) =>
      (natToBinQ (qToNatQ q pr.1), pr.2)) :=
    Computable.pair
      (computable_natToBinQ.comp ((primrec_qToNatQ q).to_comp.comp Computable.fst))
      Computable.snd
  exact (Partrec.comp hU h_f).of_eq (fun _ => rfl)

private lemma natToQDigitsQ_eq_range_map (q : ℕ) (hq : 2 ≤ q) (k n : ℕ) :
    natToQDigitsQ q hq k n =
      (List.range k).map (fun i => ⟨n / q ^ i % q, Nat.mod_lt _ (by omega)⟩) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    dsimp [natToQDigitsQ]
    rw [ih (n / q)]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    dsimp [Function.comp]
    congr 1
    · ext; dsimp; simp
    · congr 1
      funext i
      ext
      dsimp
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul]

private lemma primrec_natToQDigitsQ (q : ℕ) (hq : 2 ≤ q) : Primrec₂ (natToQDigitsQ q hq) := by
  have h_range : Primrec (fun p : ℕ × ℕ => List.range p.1) :=
    Primrec.list_range.comp Primrec.fst
  have h_n : Primrec (fun p : (ℕ × ℕ) × ℕ => p.1.2) := Primrec.snd.comp Primrec.fst
  have h_i : Primrec (fun p : (ℕ × ℕ) × ℕ => p.2) := Primrec.snd
  have h_pow := nat_pow_primrec₂.comp (Primrec.const q) h_i
  have h_div := Primrec.nat_div.comp h_n h_pow
  have h_mod := Primrec.nat_mod.comp h_div (Primrec.const q)
  have h_fin : Primrec (fun p : (ℕ × ℕ) × ℕ =>
      (⟨p.1.2 / q ^ p.2 % q, Nat.mod_lt _ (by omega)⟩ : Fin q)) :=
    Primrec.fin_val_iff.mp h_mod
  have h_elem : Primrec₂ (fun (p : ℕ × ℕ) (i : ℕ) =>
      (⟨p.2 / q ^ i % q, Nat.mod_lt _ (by omega)⟩ : Fin q)) := h_fin.to₂
  have h_map := Primrec.list_map h_range h_elem
  exact (h_map.of_eq (fun p => (natToQDigitsQ_eq_range_map q hq p.1 p.2).symm)).to₂

private lemma computable_natToQQ (q : ℕ) (hq : 2 ≤ q) : Computable (natToQQ q hq) := by
  have h_arg : Computable (fun n : ℕ => (q - 1) * n + 1) :=
    Computable₂.comp Primrec.nat_add.to_comp
      (Computable₂.comp Primrec.nat_mul.to_comp (Computable.const (q - 1)) Computable.id)
      (Computable.const 1)
  have h_L : Computable (fun n => Nat.log q ((q - 1) * n + 1)) :=
    (computable_nat_logQ q hq).comp h_arg
  have h_sub : Computable (fun n => n - geomQ q (Nat.log q ((q - 1) * n + 1))) :=
    Computable₂.comp Primrec.nat_sub.to_comp Computable.id
      ((primrec_geomQ q).to_comp.comp h_L)
  exact Computable₂.comp (primrec_natToQDigitsQ q hq).to_comp h_L h_sub

private lemma mapToBin_partrecQ (q : ℕ) (hq : 2 ≤ q) (D : QMap q) (hD : Partrec D) :
    isDecompressor (mapToBinQ q hq D) := by
  have h_h : Computable (fun (pr : BitString × BitString) =>
      (natToQQ q hq (binToNatQ pr.1), pr.2)) :=
    Computable.pair
      ((computable_natToQQ q hq).comp (primrec_binToNatQ.to_comp.comp Computable.fst))
      Computable.snd
  exact (Partrec.comp hD h_h).of_eq (fun _ => rfl)

private lemma real_logb2_powQ (q : ℕ) (hq : 2 ≤ q) (k : ℕ) :
    Real.logb 2 ((q : ℝ) ^ k) = (k : ℝ) * Real.logb 2 (q : ℝ) := by
  have _ := hq
  exact Real.logb_pow 2 (q : ℝ) k

private lemma natLog2_le_real_logb2_powQ (n : ℕ) :
    (Nat.log 2 n : ℝ) ≤ Real.logb 2 (n : ℝ) := by
  cases n with
  | zero => simp
  | succ n =>
    have hn : n + 1 ≠ 0 := by omega
    have h_le := Nat.pow_log_le_self 2 hn
    have h1 : ((2 ^ Nat.log 2 (n + 1) : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h_le
    have h2 : (0 : ℝ) < ((2 ^ Nat.log 2 (n + 1) : ℕ) : ℝ) := by positivity
    have h3 := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) h2 (by positivity)).2 h1
    have h4 : Real.logb 2 ((2 ^ Nat.log 2 (n + 1) : ℕ) : ℝ) = (Nat.log 2 (n + 1) : ℝ) := by
      push_cast
      rw [Real.logb_pow 2 2 (Nat.log 2 (n + 1))]
      have h5 : Real.logb 2 2 = 1 := by
        unfold Real.logb
        exact div_self (Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num))
      rw [h5, mul_one]
    linarith

private lemma q_pow_natLog_mul_real_logb2Q (q : ℕ) (hq : 2 ≤ q) (n : ℕ) :
    (Nat.log q ((q - 1) * n + 1) : ℝ) * Real.logb 2 (q : ℝ) ≤
      Real.logb 2 (((q - 1) * n + 1 : ℕ) : ℝ) := by
  have h_arg : (q - 1) * n + 1 ≠ 0 := by omega
  have h_le := Nat.pow_log_le_self q h_arg
  have h1 : ((q ^ Nat.log q ((q - 1) * n + 1) : ℕ) : ℝ) ≤ (((q - 1) * n + 1 : ℕ) : ℝ) :=
    by exact_mod_cast h_le
  have h2 : (0 : ℝ) < ((q ^ Nat.log q ((q - 1) * n + 1) : ℕ) : ℝ) := by positivity
  have h3 := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) h2 (by positivity)).2 h1
  have h4 : Real.logb 2 ((q ^ Nat.log q ((q - 1) * n + 1) : ℕ) : ℝ) =
      (Nat.log q ((q - 1) * n + 1) : ℝ) * Real.logb 2 (q : ℝ) := by
    push_cast
    exact real_logb2_powQ q hq _
  linarith

/-- Rescaled by `log₂ q`, a `q`-ary description length coming from a binary program of length
at most `N` exceeds `N` by at most the calibration constant. -/
private lemma natLog_mul_logb_sub_le {q L N c_mapQ c_mapBin C_val : ℕ} (hq : 2 ≤ q)
    (hC_val : C_val = ⌈Real.logb 2 (q : ℝ) + (c_mapBin : ℝ)⌉₊ +
      ⌈((c_mapQ : ℝ) + 1) * Real.logb 2 (q : ℝ) + 1⌉₊ + 1)
    {p : BitString} (hp_len : p.length ≤ N)
    (hL_le : L ≤ Nat.log q ((q - 1) * binToNatQ p + 1) + c_mapQ) :
    (L : ℝ) * Real.logb 2 (q : ℝ) - (N : ℝ) ≤ (C_val : ℝ) := by
  have h1 : (L : ℝ) * Real.logb 2 (q : ℝ) ≤
      (Nat.log q ((q - 1) * binToNatQ p + 1) : ℝ) * Real.logb 2 (q : ℝ) +
        (c_mapQ : ℝ) * Real.logb 2 (q : ℝ) := by
    have : (L : ℝ) ≤ (Nat.log q ((q - 1) * binToNatQ p + 1) : ℝ) + (c_mapQ : ℝ) :=
      by exact_mod_cast hL_le
    have h_log_pos : (0 : ℝ) ≤ Real.logb 2 (q : ℝ) :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ q by omega))
    nlinarith
  have h2 := q_pow_natLog_mul_real_logb2Q q hq (binToNatQ p)
  have h_p_bin : binToNatQ p < 2 ^ (N + 1) := by
    dsimp [binToNatQ]
    have hd := decodeBitsQ_lt_pow p
    have h1 : 2 ^ p.length ≤ 2 ^ N := Nat.pow_le_pow_right (by decide) hp_len
    have h2 : 2 ^ (N + 1) = 2 * 2 ^ N := by rw [Nat.pow_succ']
    have h3 : 2 ^ p.length - 1 + decodeBitsQ p < 2 * 2 ^ p.length - 1 := by omega
    have h4 : 2 * 2 ^ p.length - 1 ≤ 2 * 2 ^ N - 1 := by omega
    omega
  have h3 : (q - 1) * binToNatQ p + 1 ≤ q * 2 ^ (N + 1) := by
    have h1 : binToNatQ p + 1 ≤ 2 ^ (N + 1) := h_p_bin
    have h2 : (q - 1) * binToNatQ p + 1 ≤ (q - 1) * (binToNatQ p + 1) := by
      have : 1 ≤ q - 1 := by omega
      calc (q - 1) * binToNatQ p + 1
        _ ≤ (q - 1) * binToNatQ p + (q - 1) := by omega
        _ = (q - 1) * (binToNatQ p + 1) := by ring
    have h3' : (q - 1) * (binToNatQ p + 1) ≤ (q - 1) * 2 ^ (N + 1) :=
      Nat.mul_le_mul_left (q - 1) h1
    have h4 : (q - 1) * 2 ^ (N + 1) ≤ q * 2 ^ (N + 1) :=
      Nat.mul_le_mul_right (2 ^ (N + 1)) (by omega)
    omega
  have h4 : Real.logb 2 (((q - 1) * binToNatQ p + 1 : ℕ) : ℝ) ≤
      (N + 1 : ℝ) + Real.logb 2 (q : ℝ) := by
    have hpos : (0 : ℝ) < (((q - 1) * binToNatQ p + 1 : ℕ) : ℝ) := by positivity
    have h3_eq : (q - 1) * binToNatQ p + 1 ≤ 2 ^ (N + 1) * q := by
      calc (q - 1) * binToNatQ p + 1
        _ ≤ q * 2 ^ (N + 1) := h3
        _ = 2 ^ (N + 1) * q := Nat.mul_comm _ _
    have h_le_real : (((q - 1) * binToNatQ p + 1 : ℕ) : ℝ) ≤ ((2 ^ (N + 1) * q : ℕ) : ℝ) :=
      by exact_mod_cast h3_eq
    have h_log_le :=
      (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hpos (by positivity)).2 h_le_real
    have h_log_mul : Real.logb 2 (((2 ^ (N + 1) * q : ℕ) : ℝ)) =
        Real.logb 2 ((2 ^ (N + 1) : ℕ) : ℝ) + Real.logb 2 (q : ℝ) := by
      have h_a : (0 : ℝ) < ((2 ^ (N + 1) : ℕ) : ℝ) := by positivity
      have h_b : (0 : ℝ) < (q : ℝ) := by positivity
      have h_eq : (((2 ^ (N + 1) * q : ℕ) : ℝ)) = ((2 ^ (N + 1) : ℕ) : ℝ) * (q : ℝ) :=
        by push_cast; rfl
      rw [h_eq, Real.logb_mul h_a.ne' h_b.ne']
    have h_log_2pow : Real.logb 2 ((2 ^ (N + 1) : ℕ) : ℝ) = (N : ℝ) + 1 := by
      have h_eq2 : ((2 ^ (N + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (N + 1) := by push_cast; rfl
      rw [h_eq2, Real.logb_pow 2 2 (N + 1)]
      have : Real.logb 2 2 = 1 := by
        unfold Real.logb
        exact div_self (Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num))
      rw [this, mul_one]
      push_cast
      rfl
    linarith [h_log_le, h_log_mul, h_log_2pow]
  have h6 : (L : ℝ) * Real.logb 2 (q : ℝ) ≤
      (N : ℝ) + 1 + ((c_mapQ : ℝ) + 1) * Real.logb 2 (q : ℝ) := by
    linarith [h1, h2, h4]
  have h_C1 : ((c_mapQ : ℝ) + 1) * Real.logb 2 (q : ℝ) + 1 ≤ (C_val : ℝ) := by
    rw [hC_val]
    have : (0 : ℝ) ≤ Real.logb 2 (q : ℝ) :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ q by omega))
    have h1 : 0 ≤ (⌈Real.logb 2 (q : ℝ) + (c_mapBin : ℝ)⌉₊ : ℝ) := by positivity
    have h2 : ((c_mapQ : ℝ) + 1) * Real.logb 2 (q : ℝ) + 1 ≤
        (⌈((c_mapQ : ℝ) + 1) * Real.logb 2 (q : ℝ) + 1⌉₊ : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  linarith [h6, h_C1]

/-- Rescaled by `log₂ q`, a `q`-ary description of length `L` falls short of the binary
complexity `N` by at most the calibration constant. -/
private lemma sub_natLog_mul_logb_le {q L N c_mapQ c_mapBin C_val : ℕ} (hq : 2 ≤ q)
    (hC_val : C_val = ⌈Real.logb 2 (q : ℝ) + (c_mapBin : ℝ)⌉₊ +
      ⌈((c_mapQ : ℝ) + 1) * Real.logb 2 (q : ℝ) + 1⌉₊ + 1)
    {w_val : List (Fin q)} (hw_len_nat : w_val.length = L)
    (hN_le : N ≤ Nat.log 2 (qToNatQ q w_val + 1) + c_mapBin) :
    (N : ℝ) - (L : ℝ) * Real.logb 2 (q : ℝ) ≤ (C_val : ℝ) := by
  have h_qToNat_b := qToNat_boundQ q hq w_val
  have h_qToNat_le : qToNatQ q w_val + 1 ≤ q ^ (w_val.length + 1) := by
    have : qToNatQ q w_val + 1 ≤ (q - 1) * qToNatQ q w_val + 1 := by
      nlinarith [show 1 ≤ q - 1 by omega]
    omega
  have h_log2_le : Nat.log 2 (qToNatQ q w_val + 1) ≤ Nat.log 2 (q ^ (L + 1)) := by
    rw [← hw_len_nat]
    exact Nat.log_mono (by decide) (by decide) h_qToNat_le
  have h_log_real : (Nat.log 2 (qToNatQ q w_val + 1) : ℝ) ≤
      (L + 1 : ℝ) * Real.logb 2 (q : ℝ) := by
    have h_cast_pow : (((q ^ (L + 1) : ℕ) : ℝ)) = (q : ℝ) ^ (L + 1) := by push_cast; rfl
    have h_nat_le : (Nat.log 2 (q ^ (L + 1)) : ℝ) ≤ Real.logb 2 ((q ^ (L + 1) : ℕ) : ℝ) :=
      natLog2_le_real_logb2_powQ _
    have h_real_pow : Real.logb 2 ((q : ℝ) ^ (L + 1)) =
        ((L + 1 : ℕ) : ℝ) * Real.logb 2 (q : ℝ) :=
      real_logb2_powQ q hq (L + 1)
    calc (Nat.log 2 (qToNatQ q w_val + 1) : ℝ)
      _ ≤ (Nat.log 2 (q ^ (L + 1)) : ℝ) := by exact_mod_cast h_log2_le
      _ ≤ Real.logb 2 ((q ^ (L + 1) : ℕ) : ℝ) := h_nat_le
      _ = Real.logb 2 ((q : ℝ) ^ (L + 1)) := by rw [h_cast_pow]
      _ = ((L + 1 : ℕ) : ℝ) * Real.logb 2 (q : ℝ) := h_real_pow
      _ = (L + 1 : ℝ) * Real.logb 2 (q : ℝ) := by push_cast; rfl
  have h_N_real : (N : ℝ) ≤
      (L : ℝ) * Real.logb 2 (q : ℝ) + Real.logb 2 (q : ℝ) + (c_mapBin : ℝ) := by
    calc (N : ℝ)
      _ ≤ (Nat.log 2 (qToNatQ q w_val + 1) : ℝ) + (c_mapBin : ℝ) := by exact_mod_cast hN_le
      _ ≤ (L + 1 : ℝ) * Real.logb 2 (q : ℝ) + (c_mapBin : ℝ) := by linarith [h_log_real]
      _ = (L : ℝ) * Real.logb 2 (q : ℝ) + Real.logb 2 (q : ℝ) + (c_mapBin : ℝ) := by ring
  have h_C2 : Real.logb 2 (q : ℝ) + (c_mapBin : ℝ) ≤ (C_val : ℝ) := by
    rw [hC_val]
    have : (0 : ℝ) ≤ Real.logb 2 (q : ℝ) :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ q by omega))
    have h1 : 0 ≤ (⌈((c_mapQ : ℝ) + 1) * Real.logb 2 (q : ℝ) + 1⌉₊ : ℝ) := by positivity
    have h2 : Real.logb 2 (q : ℝ) + (c_mapBin : ℝ) ≤
        (⌈Real.logb 2 (q : ℝ) + (c_mapBin : ℝ)⌉₊ : ℝ) :=
      Nat.le_ceil _
    push_cast
    linarith
  linarith [h_N_real, h_C2]

/-- Complexity over a `q`-letter description alphabet, rescaled by `log₂ q`, differs from
binary plain complexity by at most an additive constant. SUV Exercise 5. -/
theorem abs_qPlainK_mul_logb_sub_cVal_le (U : Map) (hU : isOptimalConditional U)
    (q : ℕ) (hq : 2 ≤ q) (D : QMap q) (hD : IsQOptimal D) :
    ∃ k : ℕ, ∀ x : BitString,
      |((qPlainK D x).toNat : ℝ) * Real.logb 2 q - (cVal U x : ℝ)| ≤ (k : ℝ) := by
  obtain ⟨c_len, hc_len⟩ := plainK_le_length U hU
  have h_mapQ : Partrec (mapToQQ q U) := mapToQ_partrecQ q U hU.1
  obtain ⟨c_mapQ, hc_mapQ⟩ := hD.2 (mapToQQ q U) h_mapQ
  have h_mapBin : isDecompressor (mapToBinQ q hq D) := mapToBin_partrecQ q hq D hD.1
  obtain ⟨c_mapBin, hc_mapBin⟩ := hU.2 (mapToBinQ q hq D) h_mapBin
  set C_val := ⌈Real.logb 2 (q : ℝ) + (c_mapBin : ℝ)⌉₊ +
    ⌈((c_mapQ : ℝ) + 1) * Real.logb 2 (q : ℝ) + 1⌉₊ + 1
  use C_val
  intro x
  have hK_top : plainK U x ≠ ⊤ := by
    have h_le := hc_len x
    have h_top_ne : (x.length : ℕ∞) + c_len ≠ ⊤ := ENat.coe_ne_top _
    intro h_top
    rw [h_top] at h_le
    exact h_top_ne (top_le_iff.mp h_le)
  set N := (plainK U x).toNat
  have hN_eq : plainK U x = (N : ℕ∞) := (ENat.coe_toNat hK_top).symm
  have hN_cVal : (cVal U x : ℝ) = (N : ℝ) := rfl
  have h_condK_le : condK U x [] ≤ (N : ℕ∞) := by exact le_of_eq hN_eq
  obtain ⟨p, hp_len, hp_prod⟩ := (condK_le_iff U x [] N).mp h_condK_le
  have hp_mapQ_prod : x ∈ mapToQQ q U (natToQQ q hq (binToNatQ p), []) := by
    dsimp [mapToQQ]
    have h1 : qToNatQ q (natToQQ q hq (binToNatQ p)) = binToNatQ p := qToNatQ_natToQQ q hq _
    have h2 : natToBinQ (binToNatQ p) = p := natToBinQ_binToNatQ p
    rw [h1, h2]
    exact hp_prod
  have hqD_le : qPlainK D x ≤
      ((Nat.log q ((q - 1) * binToNatQ p + 1) + c_mapQ : ℕ) : ℕ∞) := by
    have h_sInf : qPlainK (mapToQQ q U) x ≤ ((natToQQ q hq (binToNatQ p)).length : ℕ∞) :=
      sInf_le (s := {n : ℕ∞ | ∃ w : List (Fin q), x ∈ mapToQQ q U (w, []) ∧
        (w.length : ℕ∞) = n})
        ⟨natToQQ q hq (binToNatQ p), hp_mapQ_prod, rfl⟩
    have h_hc : qPlainK D x ≤ qPlainK (mapToQQ q U) x + (c_mapQ : ℕ∞) := hc_mapQ x []
    have h_combined : qPlainK D x ≤
        ((natToQQ q hq (binToNatQ p)).length : ℕ∞) + (c_mapQ : ℕ∞) := by
      calc qPlainK D x
        _ ≤ qPlainK (mapToQQ q U) x + (c_mapQ : ℕ∞) := h_hc
        _ ≤ ((natToQQ q hq (binToNatQ p)).length : ℕ∞) + (c_mapQ : ℕ∞) := by gcongr
    rw [natToQQ_length] at h_combined
    exact h_combined
  have hqD_ne_top : qPlainK D x ≠ ⊤ := by
    have h_top_ne2 : ((Nat.log q ((q - 1) * binToNatQ p + 1) + c_mapQ : ℕ) : ℕ∞) ≠ ⊤ :=
      ENat.coe_ne_top _
    intro h_top
    rw [h_top] at hqD_le
    exact h_top_ne2 (top_le_iff.mp hqD_le)
  set L := (qPlainK D x).toNat
  have hL_eq : qPlainK D x = (L : ℕ∞) := (ENat.coe_toNat hqD_ne_top).symm
  have hL_le : L ≤ Nat.log q ((q - 1) * binToNatQ p + 1) + c_mapQ := by
    have h_le_coe : (L : ℕ∞) ≤
        ((Nat.log q ((q - 1) * binToNatQ p + 1) + c_mapQ : ℕ) : ℕ∞) := by
      rwa [← hL_eq]
    exact_mod_cast h_le_coe
  have h_bound_upper : (L : ℝ) * Real.logb 2 (q : ℝ) - (N : ℝ) ≤ (C_val : ℝ) :=
    natLog_mul_logb_sub_le hq rfl hp_len hL_le
  have h_nonempty :
      {n : ℕ∞ | ∃ w : List (Fin q), x ∈ D (w, []) ∧ (w.length : ℕ∞) = n}.Nonempty := by
    by_contra h_empty
    have : qPlainK D x = ⊤ := by
      unfold qPlainK qCondK
      rw [Set.not_nonempty_iff_eq_empty.mp h_empty, sInf_empty]
    exact hqD_ne_top this
  have h_mem := csInf_mem h_nonempty
  unfold qPlainK qCondK at hL_eq
  rw [hL_eq] at h_mem
  obtain ⟨w_val, hw_val_prod, hw_len_eq⟩ := h_mem
  have hw_len_nat : w_val.length = L := by exact_mod_cast hw_len_eq
  have h_bound_lower : (N : ℝ) - (L : ℝ) * Real.logb 2 (q : ℝ) ≤ (C_val : ℝ) := by
    have hp_bin_prod : x ∈ mapToBinQ q hq D (natToBinQ (qToNatQ q w_val), []) := by
      dsimp [mapToBinQ]
      rw [binToNatQ_natToBinQ, natToQQ_qToNatQ]
      exact hw_val_prod
    have h_sInf_le : condK (mapToBinQ q hq D) x [] ≤
        ((natToBinQ (qToNatQ q w_val)).length : ℕ∞) := by
      unfold condK
      exact sInf_le ⟨natToBinQ (qToNatQ q w_val), hp_bin_prod, rfl⟩
    have h_hc : condK U x [] ≤ condK (mapToBinQ q hq D) x [] + (c_mapBin : ℕ∞) :=
      hc_mapBin x []
    have h_cond_le : condK U x [] ≤
        ((natToBinQ (qToNatQ q w_val)).length : ℕ∞) + (c_mapBin : ℕ∞) := by
      calc condK U x []
        _ ≤ condK (mapToBinQ q hq D) x [] + (c_mapBin : ℕ∞) := h_hc
        _ ≤ ((natToBinQ (qToNatQ q w_val)).length : ℕ∞) + (c_mapBin : ℕ∞) := by gcongr
    have hN_le : N ≤ (natToBinQ (qToNatQ q w_val)).length + c_mapBin := by
      have h_cond_eq : condK U x [] = (N : ℕ∞) := hN_eq
      rw [h_cond_eq] at h_cond_le
      exact_mod_cast h_cond_le
    rw [natToBinQ_length] at hN_le
    exact sub_natLog_mul_logb_le hq rfl hw_len_nat hN_le
  rw [hN_cVal]
  rw [abs_le]
  constructor <;> linarith

end Kolmogorov
