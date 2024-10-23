import Mathlib.Tactic.Lemma
import Game.NaturalNumber.MyNat.Definition

namespace MyNat

def pred : MyNat → MyNat
| zero => 0
| succ n => n

lemma pred_succ (n : MyNat) : pred (succ n) = n := rfl

-- 「4. 任意の n, m ∈ ℕ について n ≠ m ならば S(n) ≠ S(m)」
theorem succ_inj (a b : MyNat) (h : succ a = succ b) : a = b := by
  rw [← pred_succ a]
  rw [h, pred_succ]

def is_zero : MyNat → Prop
| zero => True
| succ _ => False

lemma is_zero_zero : is_zero 0 = True := rfl
lemma is_zero_succ (n : MyNat) : is_zero (succ n) = False := rfl

-- 「3. 任意の n ∈ ℕ について S(n) ≠ 0」
theorem zero_ne_succ (a : MyNat) : 0 ≠ succ a := by
  intro h
  rw [← is_zero_succ a]
  rw [← h]
  rw [is_zero_zero]
  trivial
