import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Basic
import RealAnalysis.Bound.Basic

theorem Bound.Above_trans
  (subset : Set ℚ) (ub₁ : ℚ) (ub₂ : ℚ)
  (h_ub₁ : Bound.Above subset ub₁)
  (h_ub₁_le_ub₂ : ub₁ ≤ ub₂)
  : Bound.Above subset ub₂ := by
    simp [Bound.Above] at *
    intros x h_x_in_subset
    have h_x_le_ub₁ := h_ub₁ x h_x_in_subset
    apply le_trans h_x_le_ub₁
    assumption

theorem Bound.lub_le_ub_iff
  (subset : Set ℚ) (lub : ℚ) (ub : ℚ)
  (h_lub : Bound.Sup subset lub)
  : Bound.Above subset ub ↔ lub ≤ ub := by
    simp [Bound.Sup] at *
    apply Iff.intro
    · sorry
    · intro h_lub_le_ub
      exact Bound.Above_trans subset lub ub h_lub.left h_lub_le_ub
