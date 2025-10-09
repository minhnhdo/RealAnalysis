import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Basic
import RealAnalysis.Rat.Lemmas

def Set.IsBoundedAbove {t} [Preorder t] (s : Set t) (upperBound : t) := ∀ x, x ∈ s → x ≤ upperBound

def Set.Sup {t} [Preorder t] (s : Set t) (lub : t) :=
  s.IsBoundedAbove lub ∧ ∀ ub, s.IsBoundedAbove ub → lub ≤ ub

def Set.IsBoundedBelow {t} [Preorder t] (s : Set t) (lowerBound : t) := ∀ x, x ∈ s → lowerBound ≤ x

def Set.Inf {t} [Preorder t] (s : Set t) (glb : t) :=
  s.IsBoundedBelow glb ∧ ∀ lb, s.IsBoundedBelow lb → lb ≤ glb

def Set.IsComplete {t} [Preorder t] (s : Set t) :=
  ∀ ub, s.Nonempty → s.IsBoundedAbove ub → ∃ lub, s.Sup lub

example : (Finset.cons 2
            ((Finset.cons 1
              (Finset.cons (mkRat 1 2) Finset.empty (by decide))
                (by decide)))
              (by decide)).toSet.IsBoundedAbove 2 := by
  simp [Set.IsBoundedAbove] at *
  decide

example : { x : ℚ | x * x < 2 }.IsBoundedAbove (mkRat 3 2) := by
  simp [Set.IsBoundedAbove]
  intro p hp
  by_cases h : p ≤ (mkRat 3 2)
  · assumption
  · rw [not_le] at h
    have h' : (mkRat 3 2) * (mkRat 3 2) < p * p := by
      apply mul_lt_mul'' h h
      · decide
      · decide
    simp at h'
    have contra := lt_trans h' hp
    contradiction

example : { x : ℚ | 0 < x }.Inf 0 := by
  constructor
  · simp [Set.IsBoundedBelow]
    intros
    apply le_of_lt
    assumption
  · intros lb h_lb
    by_cases h : lb ≤ 0
    · assumption
    · rw [not_le] at h
      have : ¬{ x : ℚ | 0 < x }.IsBoundedBelow lb := by
        simp [Set.IsBoundedBelow]
        use lb / 2
        constructor
        · apply half_pos
          assumption
        · apply half_lt_self
          assumption
      contradiction

example : { x : ℚ | x < 0 }.Sup 0 := by
  constructor
  · simp [Set.IsBoundedAbove]
    intros
    apply le_of_lt
    assumption
  · intros ub h_ub
    by_cases h : 0 ≤ ub
    · assumption
    · rw [not_le] at h
      have : ¬ { x : ℚ | x < 0 }.IsBoundedAbove ub := by
        simp [Set.IsBoundedAbove]
        use ub / 2
        constructor
        · apply Rat.half_neg
          assumption
        · apply Rat.lt_half
          assumption
      contradiction
