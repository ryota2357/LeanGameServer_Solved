import Game.NaturalNumber.MyNat
import Game.NaturalNumber.World.Addition

namespace Game.NaturalNumber.Multiplication

open MyNat Addition

-- 1
theorem mul_one (m : MyNat) : m * 1 = m := by
  have h1 : 1 = succ 0 := rfl
  rw [h1]
  rw [mul_succ]
  rw [mul_zero, zero_add]

-- 2
theorem zero_mul (m : MyNat) : 0 * m = 0 := by
  induction m with
  | zero => rw [zero_eq_0, mul_zero]
  | succ n ih => rw [mul_succ, add_zero, ih]

-- 3
theorem succ_mul (a b : MyNat) : succ a * b = a * b + b := by
  induction b with
  | zero =>
    rw [zero_eq_0]
    rw [add_zero, mul_zero, mul_zero]
  | succ c ih =>
    rw [mul_succ, mul_succ, add_succ, add_succ]
    rw [ih, add_right_comm]

-- 4
theorem mul_comm (a b : MyNat) : a * b = b * a := by
  induction a with
  | zero =>
    rw [zero_eq_0]
    rw [mul_zero, zero_mul]
  | succ c ih =>
    rw [mul_succ, succ_mul]
    rw [ih]

-- 5
theorem one_mul (m : MyNat): 1 * m = m := by
  rw [mul_comm, mul_one]

-- 6
theorem two_mul (m : MyNat): 2 * m = m + m := by
  have h1 : 2 = succ 1 := rfl
  rw [h1]
  rw [succ_mul]
  rw [one_mul]

-- 7
theorem mul_add (a b c : MyNat) : a * (b + c) = a * b + a * c := by
  induction b with
  | zero =>
    rw [zero_eq_0]
    rw [mul_zero, zero_add, zero_add]
  | succ d ih =>
    rw [succ_add, mul_succ, mul_succ]
    rw [ih, add_right_comm]

-- 8
theorem add_mul (a b c : MyNat) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add]
  -- repeat rw [mul_comm c]
  rw [mul_comm c a, mul_comm c b]

-- 9
theorem mul_assoc (a b c : MyNat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
    rw [zero_eq_0]
    repeat rw [mul_zero]
  | succ d ih =>
    repeat rw [mul_succ]
    rw [mul_add, ih]
