import Mathlib.Data.Set.Basic

namespace Game.SetTheory.Complement

variable {U : Type}

-- 1
example {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  by_contra h3
  have := h3 h1
  -- contradiction
  exact h2 this

-- 2
theorem mem_compl_iff (A : Set U) (x : U) : x ∈ Aᶜ ↔ x ∉ A := by
  rfl

-- 3
theorem compl_subset_compl_of_subset {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  intro x h2
  rewrite [mem_compl_iff A x]
  rewrite [mem_compl_iff B x] at h2
  by_contra h3
  have := h1 h3
  contradiction

-- 4
theorem compl_compl (A : Set U) : Aᶜᶜ = A := by
  apply Set.Subset.antisymm
  . show Aᶜᶜ ⊆ A
    intro x h1
    rw [mem_compl_iff Aᶜ x] at h1
    rw [mem_compl_iff A x] at h1
    push_neg at h1
    assumption -- exact h1
  . show A ⊆ Aᶜᶜ
    intro x h1
    rw [mem_compl_iff Aᶜ x]
    rw [mem_compl_iff A x]
    push_neg
    assumption --exact h1

-- 5
example (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  apply Iff.intro
  . show A ⊆ B → Bᶜ ⊆ Aᶜ
    intro h1
    exact compl_subset_compl_of_subset h1
  . show Bᶜ ⊆ Aᶜ → A ⊆ B
    intro h1
    have h2 := compl_subset_compl_of_subset h1
    repeat rw [compl_compl] at h2
    exact h2
