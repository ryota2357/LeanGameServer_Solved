import Game.NaturalNumber.MyNat

namespace Game.NaturalNumber.Addition

open MyNat

-- 1
theorem zero_add (n : MyNat) : 0 + n = n := by
  induction n with
  | zero => rw [zero_eq_0, add_zero]
  | succ m ih => rw [add_succ, ih]

-- 2
theorem succ_add (a b : MyNat) : succ a + b = succ (a + b) := by
  induction b with
  | zero =>
    rw [zero_eq_0]
    rw [add_zero, add_zero]
  | succ c ih =>
    rw [add_succ, add_succ]
    rw [ih]

-- 3
theorem add_comm (a b : MyNat) : a + b = b + a := by
  induction b with
  | zero =>
    rw [zero_eq_0]
    rw [add_zero, zero_add]
  | succ c ih =>
    rw [add_succ, succ_add]
    rw [ih]

-- 4
theorem add_assoc (a b c : MyNat) : a + b + c = a + (b + c) := by
  induction a with
  | zero =>
    rw [zero_eq_0]
    rw [zero_add, zero_add]
  | succ d ih =>
    rw [succ_add, succ_add, succ_add]
    rw [ih]

-- 5
theorem add_right_comm (a b c : MyNat) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c]
  rw [add_assoc]
