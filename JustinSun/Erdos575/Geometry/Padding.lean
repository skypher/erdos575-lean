import JustinSun.Erdos575.Geometry.Patterns
import Mathlib.Data.Nat.Find
namespace L575G
/-- The incidence graph order associated to a field cardinality. -/ def incidenceOrder (q : ℕ) : ℕ := 2 * (q + 1) * (q ^ 2 + 1)
/-- One field-power step changes the incidence order by at most the cubic factor. -/ theorem incidenceOrder_step (p q : ℕ) (hp : 2 ≤ p) (hq : 1 ≤ q) :
    incidenceOrder (p * q) ≤ p ^ 3 * incidenceOrder q := by
  have ha : p * q + 1 ≤ p * (q + 1) := by nlinarith
  have hb : (p * q) ^ 2 + 1 ≤ p ^ 2 * (q ^ 2 + 1) := by nlinarith
  dsimp [incidenceOrder]
  calc
    2 * (p * q + 1) * ((p * q) ^ 2 + 1) ≤
        2 * ((p * (q + 1)) * (p ^ 2 * (q ^ 2 + 1))) := by
          simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 (Nat.mul_le_mul ha hb)
    _ = 2 * (p * (q + 1)) * (p ^ 2 * (q ^ 2 + 1)) := by ring
    _ = p ^ 3 * (2 * (q + 1) * (q ^ 2 + 1)) := by ring
/-- Powers of a base at least two dominate their exponents. -/ theorem exponent_le_power (p j : ℕ) (hp : 2 ≤ p) : j + 1 ≤ p ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      j + 1 + 1 ≤ (j + 1) * 2 := by omega
      _ ≤ (j + 1) * p := Nat.mul_le_mul_left _ hp
      _ ≤ p ^ j * p := Nat.mul_le_mul_right _ ih
      _ = p ^ (j + 1) := by rw [pow_succ]
/-- A largest available field power gives the cubic padding factor. -/ theorem incidenceOrder_padding (p n : ℕ) (hp : 2 ≤ p)
    (hbase : incidenceOrder p ≤ n) :
    ∃ j : ℕ, 1 ≤ j ∧ incidenceOrder (p ^ j) ≤ n ∧
      n < p ^ 3 * incidenceOrder (p ^ j) := by
  classical
  let P : ℕ → Prop := fun j => incidenceOrder (p ^ j) ≤ n
  let j := Nat.findGreatest P n
  have h1n : 1 ≤ n := by
    have hp_le : p ≤ incidenceOrder p := by
      dsimp [incidenceOrder]
      nlinarith
    omega
  have hP1 : P 1 := by simpa [P, pow_one] using hbase
  have hjpos : 1 ≤ j := by
    have := (Nat.findGreatest_pos (P := P) (k := n)).2 ⟨1, by omega, h1n, hP1⟩
    omega
  have hjP : P j := by
    have := Nat.findGreatest_spec (P := P) (m := 1) (n := n) h1n hP1
    simpa [j] using this
  have hjle : j ≤ n := by
    dsimp [j]
    exact Nat.findGreatest_le _
  have hnext : ¬ P (j + 1) := by
    by_cases hjn : j < n
    · have hmax := (Nat.findGreatest_eq_iff (P := P) (k := n) (m := j)).mp rfl
      exact hmax.2.2 (Nat.lt_succ_self j) (by omega)
    · have hEq : j = n := by omega
      intro hbad
      have hlow := exponent_le_power p (j + 1) hp
      have horder : p ^ (j + 1) ≤ incidenceOrder (p ^ (j + 1)) := by
        dsimp [incidenceOrder]
        nlinarith
      have hpowerlt : n < p ^ (j + 1) := by
        rw [hEq]
        omega
      omega
  have hstrict : n < incidenceOrder (p ^ (j + 1)) := by
    have := hnext
    dsimp [P] at this
    omega
  have hq : 1 ≤ p ^ j := by
    have : 0 < p ^ j := pow_pos (by omega) _
    omega
  have hstep := incidenceOrder_step p (p ^ j) hp hq
  have hfactor : incidenceOrder (p ^ (j + 1)) ≤
      p ^ 3 * incidenceOrder (p ^ j) := by
    simpa [pow_succ, Nat.mul_comm] using hstep
  exact ⟨j, hjpos, hjP, lt_of_lt_of_le hstrict hfactor⟩
/-- The numerical power-selection statement used for padding the witnesses. -/ def padding_statement : Prop :=
  ∀ p : ℕ, (p = 2 ∨ p = 3) → ∀ n : ℕ,
    incidenceOrder p ≤ n →
    ∃ j : ℕ, 1 ≤ j ∧ incidenceOrder (p ^ j) ≤ n ∧
      n < p ^ 3 * incidenceOrder (p ^ j)
/-- The power-selection statement holds for the two required characteristics. -/ theorem padding : padding_statement := by
  intro p hp n hn
  exact incidenceOrder_padding p n (by omega) hn
/-- The smallest characteristic-two witness has thirty vertices. -/ theorem incidenceOrder_two : incidenceOrder 2 = 30 := by
  norm_num [incidenceOrder]
/-- The smallest characteristic-three witness has eighty vertices. -/ theorem incidenceOrder_three : incidenceOrder 3 = 80 := by
  norm_num [incidenceOrder]
end L575G
