import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Basic

def Set.BoundedAbove {t} [Preorder t] (s : Set t) (upperBound : t) := ∀ x, x ∈ s → x ≤ upperBound

def Set.Sup {t} [Preorder t] (s : Set t) (lub : t) :=
  s.BoundedAbove lub ∧ ∀ ub, s.BoundedAbove ub → lub ≤ ub

def Set.BoundedBelow {t} [Preorder t] (s : Set t) (lowerBound : t) := ∀ x, x ∈ s → lowerBound ≤ x

def Set.Inf {t} [Preorder t] (s : Set t) (glb : t) :=
  s.BoundedBelow glb ∧ ∀ lb, s.BoundedBelow lb → glb ≤ lb

example : (Finset.cons 2
            ((Finset.cons 1
              (Finset.cons (mkRat 1 2) Finset.empty (by decide))
                (by decide)))
              (by decide)).toSet.BoundedAbove 2 := by
  simp [Set.BoundedAbove] at *
  decide
