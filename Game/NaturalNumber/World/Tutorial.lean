import Game.NaturalNumber.MyNat

namespace Game.NaturalNumber.Tutorial

open MyNat

theorem two_eq_succ_one : 2 = succ 1 := rfl
theorem one_eq_succ_zero : 1 = succ 0 := rfl
theorem four_eq_succ_three : 4 = succ 3 := rfl
theorem three_eq_succ_two : 3 = succ 2 := rfl

-- 1
example (x q : Nat) : 37 * x + q = 37 * x + q := by
  rfl

-- 2
example (x y : Nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]

-- 3
example : 2 = succ (succ 0) := by
  rw [two_eq_succ_one]
  rw [one_eq_succ_zero]

-- 4
example : 2 = succ (succ 0) := by
  rw [← one_eq_succ_zero]
  rw [← two_eq_succ_one]

-- 5
example (a b c : MyNat) : a + (b + 0) + (c + 0) = a + b + c := by
  -- rw [add_zero]
  -- rw [add_zero]
  repeat rw [add_zero]

-- 6
example (a b c : MyNat) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [add_zero c]
  rw [add_zero b]

-- 7
theorem succ_eq_add_one (n : MyNat) : succ n = n + 1 := by
  rw [one_eq_succ_zero]
  rw [add_succ]
  rw [add_zero]

-- 8
example : (2 : MyNat) + 2 = 4 := by
  rw [four_eq_succ_three, three_eq_succ_two, two_eq_succ_one]
  rw [add_succ]
  rw [← succ_eq_add_one]
