import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Basic

def BoundedAbove {t} [LE t] (subset : Set t) (upperBound : t) := ∀ x, x ∈ subset → x ≤ upperBound

def Bound.sup {t} [LT t] [LE t] (subset : Set t) :=
  ∃ ub, BoundedAbove subset ub → ∀ x, x ∈ subset → x < ub → ¬BoundedAbove subset x

def BoundedBelow {t} [LE t] (subset : Set t) (lowerBound : t) := ∀ x, x ∈ subset → lowerBound ≤ x

def Bound.inf {t} [LT t] [LE t] (subset : Set t) :=
  ∃ lb, BoundedBelow subset lb → ∀ x, x ∈ subset → lb < x → ¬BoundedBelow subset x

example : Bound.sup (Finset.cons 2
                      ((Finset.cons 1
                        (Finset.cons (mkRat 1 2) Finset.empty (by decide))
                        (by decide)))
                      (by decide)).toSet := by
  use 2
  intros _ _ _ h_x_lt_lub h_x_is_ub
  simp [BoundedAbove] at *
  apply Rat.not_lt.mpr h_x_is_ub.left
  exact h_x_lt_lub
