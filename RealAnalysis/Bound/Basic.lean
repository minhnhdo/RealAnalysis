import Mathlib.Data.Set.Basic
import Mathlib.Data.Rat.Init

def BoundedAbove {t} (subset : Set t) (upperBound : t) [LE t] := ∀ x, x ∈ subset → x ≤ upperBound

example : BoundedAbove {x : ℚ | x * x < 2} (mkRat 3 2) := by
  simp [BoundedAbove]
  intros x h_x_mul_x_lt_2
  sorry

def sup {t} (subset : Set t) [LT t] [LE t] :=
  ∃ ub : t, ∀ x, x ∈ subset → x < ub → ¬BoundedAbove subset x

def BoundedBelow {t} (subset : Set t) (lowerBound : t) [LE t] := ∀ x, x ∈ subset → lowerBound ≤ x
