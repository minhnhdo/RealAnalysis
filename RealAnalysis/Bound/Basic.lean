import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Basic

def BoundedAbove {t} [LE t] (subset : Set t) (upperBound : t) := ∀ x, x ∈ subset → x ≤ upperBound

def Bound.Sup {t} [LT t] [LE t] (subset : Set t) (lub : t) :=
  BoundedAbove subset lub ∧ ∀ x, x < lub → ¬BoundedAbove subset x

def BoundedBelow {t} [LE t] (subset : Set t) (lowerBound : t) := ∀ x, x ∈ subset → lowerBound ≤ x

def Bound.Inf {t} [LT t] [LE t] (subset : Set t) (lb : t) :=
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
