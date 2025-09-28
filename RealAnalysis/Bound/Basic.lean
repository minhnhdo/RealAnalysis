import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Basic

def Set.IsBoundedAbove {t} [Preorder t] (s : Set t) (upperBound : t) := ∀ x, x ∈ s → x ≤ upperBound

def Set.Sup {t} [Preorder t] (s : Set t) (lub : t) :=
  s.IsBoundedAbove lub ∧ ∀ ub, s.IsBoundedAbove ub → lub ≤ ub

def Set.IsBoundedBelow {t} [Preorder t] (s : Set t) (lowerBound : t) := ∀ x, x ∈ s → lowerBound ≤ x

def Set.Inf {t} [Preorder t] (s : Set t) (glb : t) :=
  s.IsBoundedBelow glb ∧ ∀ lb, s.IsBoundedBelow lb → glb ≤ lb

def Set.IsComplete {t} [Preorder t] (s : Set t) :=
  ∀ ub, s.Nonempty → s.IsBoundedAbove ub → ∃ lub, s.Sup lub

example : (Finset.cons 2
            ((Finset.cons 1
              (Finset.cons (mkRat 1 2) Finset.empty (by decide))
                (by decide)))
              (by decide)).toSet.IsBoundedAbove 2 := by
  simp [Set.IsBoundedAbove] at *
  decide
