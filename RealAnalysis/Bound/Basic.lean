import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Basic

namespace Bound

def Above (subset : Set ℚ) (upperBound : ℚ) := ∀ x, x ∈ subset → x ≤ upperBound

def Sup (subset : Set ℚ) (lub : ℚ) :=
  Above subset lub ∧ ∀ x, x < lub → ¬Above subset x

def Below (subset : Set ℚ) (lowerBound : ℚ) := ∀ x, x ∈ subset → lowerBound ≤ x

def Inf (subset : Set ℚ) (glb : ℚ) :=
  Below subset glb ∧ ∀ x, glb < x → ¬Below subset x

end Bound

example : Bound.Sup (Finset.cons 2
                      ((Finset.cons 1
                        (Finset.cons (mkRat 1 2) Finset.empty (by decide))
                        (by decide)))
                      (by decide)).toSet 2 := by
  simp [Bound.Sup] at *
  apply And.intro
  · simp [Bound.Above] at *
    decide
  · intros x h_x_lt_lub h_x_is_ub
    simp [Bound.Above] at *
    have not_x_lt_lub := Rat.not_lt.mpr h_x_is_ub.left
    contradiction
