import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Basic

def Set.BoundedAbove (subset : Set ℚ) (upperBound : ℚ) := ∀ x, x ∈ subset → x ≤ upperBound

def Set.Sup (subset : Set ℚ) (lub : ℚ) :=
  subset.BoundedAbove lub ∧ ∀ ub, subset.BoundedAbove ub → lub ≤ ub

def Set.BoundedBelow (subset : Set ℚ) (lowerBound : ℚ) := ∀ x, x ∈ subset → lowerBound ≤ x

def Set.Inf (subset : Set ℚ) (glb : ℚ) :=
  subset.BoundedBelow glb ∧ ∀ lb, subset.BoundedBelow lb → glb ≤ lb

example : (Finset.cons 2
            ((Finset.cons 1
              (Finset.cons (mkRat 1 2) Finset.empty (by decide))
                (by decide)))
              (by decide)).toSet.BoundedAbove 2 := by
  simp [Set.BoundedAbove] at *
  decide
