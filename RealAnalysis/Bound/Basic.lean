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

example : { x : ℚ | 0 < x }.Inf 0 := by
  constructor
  · simp [Set.IsBoundedBelow]
    intros
    apply Rat.le_of_lt
    assumption
  · intros lb h_lb
    cases @Rat.le_total lb 0 with
    | inl =>
      assumption
    | inr zero_le_lb =>
      rw [le_iff_eq_or_lt] at zero_le_lb
      cases zero_le_lb with
      | inl zero_eq_lb =>
        rw [le_iff_eq_or_lt]
        left
        rw [zero_eq_lb]
      | inr zero_lt_lb =>
        have not_s_bounded_by_lb : ¬ { x : ℚ | 0 < x }.IsBoundedBelow lb := by
          simp [Set.IsBoundedBelow]
          use lb * (mkRat 1 2)
          constructor
          · apply Rat.mul_pos
            · assumption
            · decide
          · nth_rw 2 [← @Rat.mul_one lb]
            apply Rat.mul_lt_mul_of_pos_left
            · decide
            · assumption
        contradiction
