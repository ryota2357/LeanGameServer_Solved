import Game.NaturalNumber.MyNat
import Game.NaturalNumber.World.Tutorial
import Game.NaturalNumber.World.Addition
import Game.NaturalNumber.World.Multiplication

namespace Game.NaturalNumber.Power

open MyNat Tutorial Addition Multiplication

-- 1
theorem zero_pow_zero : (0 : MyNat) ^ 0 = 1 := by
  rw [pow_zero]

-- 2
theorem zero_pow_succ (m : MyNat) : (0 : MyNat) ^ (succ m) = 0 := by
  rw [pow_succ, mul_zero]

-- 3
theorem pow_one (a : MyNat) : a ^ 1 = a := by
  rw [one_eq_succ_zero]
  rw [pow_succ, pow_zero, one_mul]

-- 4
theorem one_pow (m : MyNat) : (1 : MyNat) ^ m = 1 := by
  induction m with
  | zero => rw [zero_eq_0, pow_zero]
  | succ n ih => rw [pow_succ, ih, mul_one]
-- (4)
theorem _one_pow (m: MyNat) : (1 : MyNat) ^ m = 1 := by
  match m with
  | zero => rw [zero_eq_0, pow_zero]
  | succ n => rw [pow_succ, one_pow, mul_one]

-- 5
theorem pow_two (a : MyNat) : a ^ 2 = a * a := by
  rw [two_eq_succ_one, pow_succ]
  rw [pow_one]

-- 6
theorem pow_add (a m n : MyNat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero =>
    rw [zero_eq_0]
    rw [add_zero, pow_zero, mul_one]
  | succ n ih =>
    rw [add_succ, pow_succ, pow_succ, ih, mul_assoc]

-- 7
theorem mul_pow (a b n : MyNat) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero =>
    rw [zero_eq_0]
    repeat rw [pow_zero]
    rw [mul_one]
  | succ n ih =>
    repeat rw [pow_succ]
    rw [ih]
    repeat rw [mul_assoc]
    rw [mul_comm a  (_ * b)]
    rw [mul_assoc, mul_comm b a]

-- 8
theorem pow_pow (a m n : MyNat) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero =>
    rw [zero_eq_0]
    rw [mul_zero, pow_zero, pow_zero]
  | succ n ih =>
    rw [pow_succ]
    rw [ih]
    rw [← pow_add, mul_succ]

-- 9
-- (a + b)² = a² + b² + 2ab
theorem add_sq (a b : MyNat) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw [two_mul]
  repeat rw [pow_two]
  rw [mul_add]
  repeat rw [add_mul]
  rw [mul_comm b a]
  -- aa + ab + (ab + bb) = aa + bb + (ab + ab)
  -- add_comm:       1 + 2 = 2 + 1
  -- add_assoc:      1 + 2 + 3 = 1 + (2 + 3)
  -- add_right_comm: 1 + 2 + 3 = 1 + 3 + 2
  rw [add_comm (a * b) (b * b)]
  -- aa + ab + (bb + ab) = aa + bb + (ab + ab)
  rw [← add_assoc]
  -- aa + ab + bb + ab = aa + bb + (ab + ab)
  rw [add_right_comm (a * a) (a * b) (b * b)]
  -- aa + bb + ab + ab = aa + bb + (ab + ab)
  rw [add_assoc]

-- 10
-- example (a b c n : MyNat) : (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3) := by
--   sorry
