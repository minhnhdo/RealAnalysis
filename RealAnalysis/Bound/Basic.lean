import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Basic

def Set.BoundedAbove (s : Set ℚ) (upperBound : ℚ) := ∀ x, x ∈ s → x ≤ upperBound

def Set.Sup (s : Set ℚ) (lub : ℚ) := s.BoundedAbove lub ∧ ∀ ub, s.BoundedAbove ub → lub ≤ ub

def Set.BoundedBelow (s : Set ℚ) (lowerBound : ℚ) := ∀ x, x ∈ s → lowerBound ≤ x

def Set.Inf (s : Set ℚ) (glb : ℚ) := s.BoundedBelow glb ∧ ∀ lb, s.BoundedBelow lb → glb ≤ lb

example : (Finset.cons 2
            ((Finset.cons 1
              (Finset.cons (mkRat 1 2) Finset.empty (by decide))
                (by decide)))
              (by decide)).toSet.BoundedAbove 2 := by
  simp [Set.BoundedAbove] at *
  decide
