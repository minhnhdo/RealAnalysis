import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Basic

def BoundedAbove {t} (subset : Set t) (upperBound : t) [LE t] := ∀ x, x ∈ subset → x ≤ upperBound

def Bound.sup {t} (subset : Set t) [LT t] [LE t] :=
  ∃ ub : t, ∀ x, x ∈ subset → x < ub → ¬BoundedAbove subset x

def BoundedBelow {t} (subset : Set t) (lowerBound : t) [LE t] := ∀ x, x ∈ subset → lowerBound ≤ x

def Bound.inf {t} (subset : Set t) [LT t] [LE t] :=
  ∃ lb : t, ∀ x, x ∈ subset → x > lb → ¬BoundedBelow subset x
