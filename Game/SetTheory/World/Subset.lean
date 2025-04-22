import Mathlib.Data.Set.Basic

namespace Game.SetTheory.Subset

variable {U : Type}

-- 1
example (x : U) (A : Set U) (h : x ∈ A) : x ∈ A := by
  exact h

-- 2
example (x : U) (A B : Set U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
  exact h1 h2

-- 3
example (x : U) (A B C : Set U) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
  -- exact h2 (h1 h3)
  have h4 : x ∈ B := h1 h3
  exact h2 h4

-- 4
example {x : U} {A B C : Set U} (h1 : A ⊆ B) (h2 : x ∈ B → x ∈ C) : x ∈ A → x ∈ C := by
  -- intro h3
  -- apply h2
  -- exact h1 h3
  intro h3
  exact h2 (h1 h3)

-- 5
theorem refl (A : Set U) : A ⊆ A := by
  intro x
  intro h
  exact h

-- 6
theorem trans {A B C : Set U} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x h
  exact h2 (h1 h)
