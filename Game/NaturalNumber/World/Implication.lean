import Mathlib.Tactic.ApplyAt
import Game.NaturalNumber.MyNat
import Game.NaturalNumber.World.Tutorial
import Game.NaturalNumber.World.Addition

namespace Game.NaturalNumber.Implication

open MyNat Tutorial Addition

-- 1
set_option linter.unusedVariables false in
example (x y z : MyNat) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
  exact h1

-- 2
example (x : MyNat) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  repeat rw [zero_add] at h
  exact h

-- 3
example (x y : MyNat) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  apply h2 at h1
  exact h1

-- 4
example (x : MyNat) (h : x + 1 = 4) : x = 3 := by
  rw [four_eq_succ_three] at h
  rw [← succ_eq_add_one] at h
  apply succ_inj at h
  exact h

-- 5
example (x : MyNat) (h : x + 1 = 4) : x = 3 := by
  apply succ_inj
  rw [succ_eq_add_one]
  rw [four_eq_succ_three] at h
  exact h

-- 6
example (x : MyNat) : x = 37 → x = 37 := by
  intro h
  exact h

-- 7
example (x : MyNat) : x + 1 = y + 1 → x = y := by
  -- repeat rw [← succ_eq_add_one]
  -- apply succ_inj
  intro h
  apply succ_inj
  repeat rw [succ_eq_add_one]
  exact h

-- 8
example (x y : MyNat) (h1 : x = y) (h2 : x ≠ y) : False := by
  apply h2 -- x = y → False
  exact h1

-- 9
theorem zero_ne_one : (0 : MyNat) ≠ 1 := by
  -- rw [one_eq_succ_zero]
  -- apply zero_ne_succ
  intro h
  rw [one_eq_succ_zero] at h
  apply zero_ne_succ at h
  exact h

-- 10
theorem one_ne_zero : (1 : MyNat) ≠ 0 := by
  symm
  -- apply zero_ne_one
  exact zero_ne_one

-- 11
-- 2 + 2 ≠ 5
example : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by
  repeat rw [add_succ]
  rw [add_zero]
  intro h
  repeat apply succ_inj at h
  apply zero_ne_succ at h
  exact h
