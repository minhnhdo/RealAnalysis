import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Basic
import RealAnalysis.Bound.Basic

theorem Set.BoundedAbove_trans
  (subset : Set ℚ) (ub₁ : ℚ) (ub₂ : ℚ)
  (h_ub₁ : subset.BoundedAbove ub₁)
  (h_ub₁_le_ub₂ : ub₁ ≤ ub₂)
  : subset.BoundedAbove ub₂ := by
    simp [Set.BoundedAbove] at *
    intros x h_x_in_subset
    have h_x_le_ub₁ := h_ub₁ x h_x_in_subset
    apply le_trans h_x_le_ub₁
    assumption

theorem Set.Sup_le_ub_iff
  (subset : Set ℚ) (lub : ℚ) (ub : ℚ)
  (h_lub : subset.Sup lub)
  : subset.BoundedAbove ub ↔ lub ≤ ub := by
    apply Iff.intro
    · sorry
    · exact subset.BoundedAbove_trans lub ub h_lub.left
