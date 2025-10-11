import Mathlib.Data.Real.Basic

universe u

@[ext]
class Dist (t : Type u) where
  dist : t → t → ℝ

export Dist (dist)

class MetricSpace (t : Type u) extends Dist t where
  dist_nonneg (p q : t) : 0 ≤ dist p q
  dist_eq_zero (p q : t) : dist p q = 0 ↔ p = q
  dist_triangle (p q r : t) : dist p r ≤ dist p q + dist q r

instance : MetricSpace ℝ where
  dist p q := |p - q|
  dist_nonneg p q := by simp
  dist_eq_zero p q := by
    simp
    constructor
    · exact eq_of_sub_eq_zero
    · intro h
      rw [h]
      simp
  dist_triangle p q r := abs_sub_le p q r

namespace Metric

variable {t : Type u} [MetricSpace t]

def ball (x : t) (r : ℝ) : Set t := { y : t | dist x y < r }

def closedBall (x : t) (r : ℝ) : Set t := { y : t | dist x y ≤ r }

def LimitPoint (p : t) (s : Set t) := ∀ r, ∃ q, q ∈ ball p r ∧ q ≠ p → q ∈ s

end Metric
