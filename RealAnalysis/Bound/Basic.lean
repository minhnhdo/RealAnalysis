import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Basic

def BoundedAbove (subset : Set ℚ) (upperBound : ℚ) := ∀ x, x ∈ subset → x ≤ upperBound

def Bound.Sup (subset : Set ℚ) (ub : ℚ) :=
  BoundedAbove subset ub → ∀ x, x < ub → ¬BoundedAbove subset x

def BoundedBelow (subset : Set ℚ) (lowerBound : ℚ) := ∀ x, x ∈ subset → lowerBound ≤ x

def Bound.Inf (subset : Set ℚ) (lb : ℚ) :=
  BoundedBelow subset lb → ∀ x, lb < x → ¬BoundedBelow subset x

example : Bound.Sup (Finset.cons 2
                      ((Finset.cons 1
                        (Finset.cons (mkRat 1 2) Finset.empty (by decide))
                        (by decide)))
                      (by decide)).toSet 2 := by
  intros _ _ h_x_lt_lub h_x_is_ub
  simp [BoundedAbove] at *
  have not_x_lt_lub := Rat.not_lt.mpr h_x_is_ub.left
  contradiction
