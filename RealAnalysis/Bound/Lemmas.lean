import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Basic
import RealAnalysis.Bound.Basic

theorem Set.BoundedAbove_trans
  (subset : Set ℚ) (ub₁ ub₂ : ℚ)
  (h_ub₁ : subset.BoundedAbove ub₁)
  (h_ub₁_le_ub₂ : ub₁ ≤ ub₂)
  : subset.BoundedAbove ub₂ := by
    simp [Set.BoundedAbove] at *
    intros x h_x_in_subset
    have h_x_le_ub₁ := h_ub₁ x h_x_in_subset
    apply le_trans h_x_le_ub₁
    assumption

theorem Set.Sup_le_ub_iff
  (subset : Set ℚ) (lub ub : ℚ)
  (h_lub : subset.Sup lub)
  :  lub ≤ ub ↔ subset.BoundedAbove ub := by
    apply Iff.intro
    · exact subset.BoundedAbove_trans lub ub h_lub.left
    · intro h_ub
      simp [Set.Sup] at *
      exact h_lub.right ub h_ub

theorem Set.Sup_le_bound_iff
  (subset : Set ℚ) (lub b : ℚ) (h_lub : subset.Sup lub)
  : (∀ x, x ∈ subset → x ≤ b) ↔ lub ≤ b := by
    simp [Set.Sup] at *
    apply Iff.intro
    · intro h_b
      apply h_lub.right
      assumption
    · intros h_lub_le_b
      apply subset.BoundedAbove_trans lub b
      · exact h_lub.left
      · assumption

theorem Set.lt_BoundedAbove
  (subset : Set ℚ) (b : ℚ)
  : (∀ x, x ∈ subset → x < b) → subset.BoundedAbove b := by
    intros h_lt x h_x_in_subset
    apply Rat.le_of_lt
    exact h_lt x h_x_in_subset

theorem Set.lt_Sup_le
  (subset : Set ℚ) (lub b : ℚ) (h_lub : subset.Sup lub)
  : (∀ x, x ∈ subset → x < b) → lub ≤ b := by
    intro h_lt
    apply h_lub.right
    exact subset.lt_BoundedAbove b h_lt

theorem Set.lt_Sup
  (subset : Set ℚ) (b lub : ℚ) (h_lub : subset.Sup lub) (h_lt : b < lub)
  : ¬subset.BoundedAbove b := by
    intro h_ub
    have h_lub_le_b := h_lub.right b h_ub
    have h_not_lub_le_b := LT.lt.not_ge h_lt
    contradiction

theorem Set.subset_imp_Sup_le
  (s₁ s₂ : Set ℚ) (lub₁ lub₂ : ℚ)
  (h_lub₁ : s₁.Sup lub₁) (h_lub₂ : s₂.Sup lub₂) (h_subset : s₁ ⊆ s₂)
  : lub₁ ≤ lub₂ := by
    simp [Set.Sup] at *
    have s₁_bounded_by_lub₂ : s₁.BoundedAbove lub₂ := by
      intro _ h_x_in_s₁
      apply h_lub₂.left
      apply h_subset
      assumption
    exact h_lub₁.right lub₂ s₁_bounded_by_lub₂
