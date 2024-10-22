import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Game.NaturalNumber.MyNat
import Game.NaturalNumber.World.Addition

namespace Game.NaturalNumber.AdvancedAddition

open MyNat Addition

-- 1
theorem add_right_cancel (a b n : MyNat) : a + n = b + n → a = b := by
  intro h
  induction n with
  | zero =>
    rw [zero_eq_0, add_zero, add_zero] at h
    exact h
  | succ n ih =>
    repeat rw [add_succ] at h
    apply succ_inj at h
    apply ih at h
    exact h

-- 2
theorem add_left_cancel (a b n : MyNat) : n + a = n + b → a = b := by
  repeat rw [add_comm n]
  apply add_right_cancel

-- 3
theorem add_left_eq_self (x y : MyNat) : x + y = y → x = 0 := by
  nth_rewrite 2 [← zero_add y]
  apply add_right_cancel

-- 4
theorem add_right_eq_self (x y : MyNat) : x + y = x → y = 0 := by
  rw [add_comm]
  apply add_left_eq_self

-- 5
theorem add_right_eq_zero (a b : MyNat) : a + b = 0 → a = 0 := by
  intro h
  cases b with
  | zero =>
    rw [zero_eq_0, add_zero] at h
    exact h
  | succ b =>
    rw [add_succ] at h
    symm at h
    apply zero_ne_succ at h
    cases h

-- 6
theorem add_left_eq_zero (a b : MyNat) : a + b = 0 → b = 0 := by
  rw [add_comm]
  apply add_right_eq_zero
