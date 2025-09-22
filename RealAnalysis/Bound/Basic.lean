import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Basic
import Mathlib.Order.Defs.PartialOrder

def BoundedAbove (subset : Set ℚ) (upperBound : ℚ) := ∀ x, x ∈ subset → x ≤ upperBound

def Bound.Sup (subset : Set ℚ) (lub : ℚ) :=
  BoundedAbove subset lub ∧ ∀ x, x < lub → ¬BoundedAbove subset x

def BoundedBelow (subset : Set ℚ) (lowerBound : ℚ) := ∀ x, x ∈ subset → lowerBound ≤ x

def Bound.Inf (subset : Set ℚ) (lb : ℚ) :=
  BoundedBelow subset lb ∧ ∀ x, lb < x → ¬BoundedBelow subset x

example : Bound.Sup (Finset.cons 2
                      ((Finset.cons 1
                        (Finset.cons (mkRat 1 2) Finset.empty (by decide))
                        (by decide)))
                      (by decide)).toSet 2 := by
  simp [Bound.Sup] at *
  apply And.intro
  · simp [BoundedAbove] at *
    decide
  · intros x h_x_lt_lub h_x_is_ub
    simp [BoundedAbove] at *
    have not_x_lt_lub := Rat.not_lt.mpr h_x_is_ub.left
    contradiction

theorem BoundedAbove_trans
  (subset : Set ℚ) (ub₁ : ℚ) (ub₂ : ℚ)
  (h_ub₁ : BoundedAbove subset ub₁)
  (h_ub₁_le_ub₂ : ub₁ ≤ ub₂)
  : BoundedAbove subset ub₂ := by
    simp [BoundedAbove] at *
    intros x h_x_in_subset
    have h_x_le_ub₁ := h_ub₁ x h_x_in_subset
    apply le_trans h_x_le_ub₁
    assumption
